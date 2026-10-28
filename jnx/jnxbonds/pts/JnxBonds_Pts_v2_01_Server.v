From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japannext Securities 

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

Module JnxBondsPtsV201Server.

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

    (** A System Event Message signals a Japannext PTS system-wide event *)
    Record t := {
      timestamp : N;
      system_event : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (system_event record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (system_event record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (system_event_value, bytes) =>
              Some ({| timestamp := timestamp_value; system_event := system_event_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SystemEventMessage.

  Module OrderAcceptedMessage.

    (** An Order Accepted Message acknowledges the receipt and acceptance of a valid Enter Order Message *)
    Record t := {
      timestamp : N;
      order_token : N;
      client_reference : list byte;
      buy_sell_indicator : list byte;
      quantity : N;
      orderbook_id : N;
      group : list byte;
      price : N;
      time_in_force : N;
      firm_id : N;
      display : list byte;
      capacity : list byte;
      order_number : N;
      minimum_quantity : N;
      order_state : list byte;
      order_classification : list byte;
      cash_margin_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_token record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (client_reference record) = 10 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (group record) = 4 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 4)%N /\
      (firm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (display record) = 1 /\
      Datatypes.length (capacity record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_state record) = 1 /\
      Datatypes.length (order_classification record) = 1 /\
      Datatypes.length (cash_margin_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (order_token record) ++
      encode_bytes 10 (client_reference record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (orderbook_id record) ++
      encode_bytes 4 (group record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (time_in_force record) ++
      encode_uint 4 (firm_id record) ++
      encode_bytes 1 (display record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (minimum_quantity record) ++
      encode_bytes 1 (order_state record) ++
      encode_bytes 1 (order_classification record) ++
      encode_bytes 1 (cash_margin_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (client_reference_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (buy_sell_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (orderbook_id_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (group_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (time_in_force_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (firm_id_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (display_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (capacity_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (order_number_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (minimum_quantity_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (order_state_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (order_classification_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (cash_margin_type_value, bytes) =>
                                                                          Some ({| timestamp := timestamp_value; order_token := order_token_value; client_reference := client_reference_value; buy_sell_indicator := buy_sell_indicator_value; quantity := quantity_value; orderbook_id := orderbook_id_value; group := group_value; price := price_value; time_in_force := time_in_force_value; firm_id := firm_id_value; display := display_value; capacity := capacity_value; order_number := order_number_value; minimum_quantity := minimum_quantity_value; order_state := order_state_value; order_classification := order_classification_value; cash_margin_type := cash_margin_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAcceptedMessage.

  Module OrderReplacedMessage.

    (** An Order Replaced Message acknowledges the receipt and acceptance of a valid Replace Order Message *)
    Record t := {
      timestamp : N;
      replacement_order_token : N;
      buy_sell_indicator : list byte;
      quantity : N;
      orderbook_id : N;
      group : list byte;
      price : N;
      time_in_force : N;
      display : list byte;
      order_number : N;
      minimum_quantity : N;
      order_state : list byte;
      previous_order_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (replacement_order_token record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (group record) = 4 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (display record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_state record) = 1 /\
      (previous_order_token record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (replacement_order_token record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (orderbook_id record) ++
      encode_bytes 4 (group record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (time_in_force record) ++
      encode_bytes 1 (display record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (minimum_quantity record) ++
      encode_bytes 1 (order_state record) ++
      encode_uint 4 (previous_order_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (replacement_order_token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (buy_sell_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (orderbook_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (group_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (time_in_force_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (display_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (order_number_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (minimum_quantity_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (order_state_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (previous_order_token_value, bytes) =>
                                                          Some ({| timestamp := timestamp_value; replacement_order_token := replacement_order_token_value; buy_sell_indicator := buy_sell_indicator_value; quantity := quantity_value; orderbook_id := orderbook_id_value; group := group_value; price := price_value; time_in_force := time_in_force_value; display := display_value; order_number := order_number_value; minimum_quantity := minimum_quantity_value; order_state := order_state_value; previous_order_token := previous_order_token_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderReplacedMessage.

  Module OrderCanceledMessage.

    (** An Order Canceled Message denotes that an order has been canceled *)
    Record t := {
      timestamp : N;
      order_token : N;
      decrement_quantity : N;
      order_canceled_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_token record < 256 ^ N.of_nat 4)%N /\
      (decrement_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_canceled_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (order_token record) ++
      encode_uint 4 (decrement_quantity record) ++
      encode_bytes 1 (order_canceled_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (decrement_quantity_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_canceled_reason_value, bytes) =>
                      Some ({| timestamp := timestamp_value; order_token := order_token_value; decrement_quantity := decrement_quantity_value; order_canceled_reason := order_canceled_reason_value |}, bytes)
                  end
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

  End OrderCanceledMessage.

  Module OrderAiqCanceledMessage.

    (** An Order AIQ Canceled Message denotes that an order has been canceled by Japannext PTS to prevent a self-trade *)
    Record t := {
      timestamp : N;
      order_token : N;
      decrement_quantity : N;
      order_canceled_reason : list byte;
      quantity_prevented_from_trading : N;
      execution_price : N;
      liquidity_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_token record < 256 ^ N.of_nat 4)%N /\
      (decrement_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_canceled_reason record) = 1 /\
      (quantity_prevented_from_trading record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (order_token record) ++
      encode_uint 4 (decrement_quantity record) ++
      encode_bytes 1 (order_canceled_reason record) ++
      encode_uint 4 (quantity_prevented_from_trading record) ++
      encode_uint 4 (execution_price record) ++
      encode_bytes 1 (liquidity_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (decrement_quantity_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_canceled_reason_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_prevented_from_trading_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (execution_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (liquidity_indicator_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; order_token := order_token_value; decrement_quantity := decrement_quantity_value; order_canceled_reason := order_canceled_reason_value; quantity_prevented_from_trading := quantity_prevented_from_trading_value; execution_price := execution_price_value; liquidity_indicator := liquidity_indicator_value |}, bytes)
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAiqCanceledMessage.

  Module OrderExecutedWithCounterPartyMessage.

    (** An Order Executed with Counter Party Message denotes that all or part of an order has been executed *)
    Record t := {
      timestamp : N;
      order_token : N;
      executed_quantity : N;
      execution_price : N;
      liquidity_indicator : list byte;
      counter_party : list byte;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_token record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_indicator record) = 1 /\
      Datatypes.length (counter_party record) = 12 /\
      (match_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (order_token record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (execution_price record) ++
      encode_bytes 1 (liquidity_indicator record) ++
      encode_bytes 12 (counter_party record) ++
      encode_uint 8 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (execution_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (liquidity_indicator_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (counter_party_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (match_number_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; order_token := order_token_value; executed_quantity := executed_quantity_value; execution_price := execution_price_value; liquidity_indicator := liquidity_indicator_value; counter_party := counter_party_value; match_number := match_number_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithCounterPartyMessage.

  Module OrderRejectedMessage.

    (** An Order Rejected Message may be sent in response to an Enter Order Message if the order cannot be accepted *)
    Record t := {
      timestamp : N;
      order_token : N;
      order_rejected_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_token record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_rejected_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (order_token record) ++
      encode_bytes 1 (order_rejected_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_rejected_reason_value, bytes) =>
                  Some ({| timestamp := timestamp_value; order_token := order_token_value; order_rejected_reason := order_rejected_reason_value |}, bytes)
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

  End OrderRejectedMessage.

End JnxBondsPtsV201Server.
