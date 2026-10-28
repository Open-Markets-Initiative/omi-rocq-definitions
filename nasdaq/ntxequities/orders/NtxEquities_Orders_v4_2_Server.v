From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) BX Orders

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

Module NtxEquitiesOrdersV42Server.

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

    Record t := {
      timestamp : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| timestamp := timestamp_value; event_code := event_code_value |}, bytes)
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

  Module AcceptedMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      buy_sell_indicator : list byte;
      shares : N;
      stock : list byte;
      price : N;
      time_in_force : N;
      firm : list byte;
      display : list byte;
      order_reference_number : N;
      capacity : list byte;
      intermarket_sweep_eligibility : list byte;
      minimum_quantity : N;
      cross_type : list byte;
      order_state : list byte;
      bbo_weight_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm record) = 4 /\
      Datatypes.length (display record) = 1 /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (intermarket_sweep_eligibility record) = 1 /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (order_state record) = 1 /\
      Datatypes.length (bbo_weight_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (time_in_force record) ++
      encode_bytes 4 (firm record) ++
      encode_bytes 1 (display record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (intermarket_sweep_eligibility record) ++
      encode_uint 4 (minimum_quantity record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (order_state record) ++
      encode_bytes 1 (bbo_weight_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (buy_sell_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (shares_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (stock_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (time_in_force_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (firm_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (display_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (order_reference_number_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (capacity_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (intermarket_sweep_eligibility_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (minimum_quantity_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (cross_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (order_state_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (bbo_weight_indicator_value, bytes) =>
                                                                      Some ({| timestamp := timestamp_value; order_token := order_token_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; time_in_force := time_in_force_value; firm := firm_value; display := display_value; order_reference_number := order_reference_number_value; capacity := capacity_value; intermarket_sweep_eligibility := intermarket_sweep_eligibility_value; minimum_quantity := minimum_quantity_value; cross_type := cross_type_value; order_state := order_state_value; bbo_weight_indicator := bbo_weight_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AcceptedMessage.

  Module ReplacedMessage.

    Record t := {
      timestamp : N;
      replacement_order_token : list byte;
      buy_sell_indicator : list byte;
      shares : N;
      stock : list byte;
      price : N;
      time_in_force : N;
      firm : list byte;
      display : list byte;
      order_reference_number : N;
      capacity : list byte;
      intermarket_sweep_eligibility : list byte;
      minimum_quantity : N;
      cross_type : list byte;
      order_state : list byte;
      previous_order_token : list byte;
      bbo_weight_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (replacement_order_token record) = 14 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm record) = 4 /\
      Datatypes.length (display record) = 1 /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (intermarket_sweep_eligibility record) = 1 /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (order_state record) = 1 /\
      Datatypes.length (previous_order_token record) = 14 /\
      Datatypes.length (bbo_weight_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (replacement_order_token record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (time_in_force record) ++
      encode_bytes 4 (firm record) ++
      encode_bytes 1 (display record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (intermarket_sweep_eligibility record) ++
      encode_uint 4 (minimum_quantity record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (order_state record) ++
      encode_bytes 14 (previous_order_token record) ++
      encode_bytes 1 (bbo_weight_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (replacement_order_token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (buy_sell_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (shares_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (stock_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (time_in_force_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (firm_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (display_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (order_reference_number_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (capacity_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (intermarket_sweep_eligibility_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (minimum_quantity_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (cross_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (order_state_value, bytes) =>
                                                                  match decode_bytes 14 bytes with
                                                                  | None => None
                                                                  | Some (previous_order_token_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (bbo_weight_indicator_value, bytes) =>
                                                                          Some ({| timestamp := timestamp_value; replacement_order_token := replacement_order_token_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; time_in_force := time_in_force_value; firm := firm_value; display := display_value; order_reference_number := order_reference_number_value; capacity := capacity_value; intermarket_sweep_eligibility := intermarket_sweep_eligibility_value; minimum_quantity := minimum_quantity_value; cross_type := cross_type_value; order_state := order_state_value; previous_order_token := previous_order_token_value; bbo_weight_indicator := bbo_weight_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplacedMessage.

  Module CanceledMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      decrement_shares : N;
      canceled_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (decrement_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (canceled_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (decrement_shares record) ++
      encode_bytes 1 (canceled_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (decrement_shares_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (canceled_reason_value, bytes) =>
                      Some ({| timestamp := timestamp_value; order_token := order_token_value; decrement_shares := decrement_shares_value; canceled_reason := canceled_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CanceledMessage.

  Module AiqCanceledMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      decrement_shares : N;
      aiq_canceled_reason : list byte;
      quantity_prevented_from_trading : N;
      execution_price : N;
      liquidity_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (decrement_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (aiq_canceled_reason record) = 1 /\
      (quantity_prevented_from_trading record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (decrement_shares record) ++
      encode_bytes 1 (aiq_canceled_reason record) ++
      encode_uint 4 (quantity_prevented_from_trading record) ++
      encode_uint 4 (execution_price record) ++
      encode_bytes 1 (liquidity_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (decrement_shares_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (aiq_canceled_reason_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_prevented_from_trading_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (execution_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (liquidity_flag_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; order_token := order_token_value; decrement_shares := decrement_shares_value; aiq_canceled_reason := aiq_canceled_reason_value; quantity_prevented_from_trading := quantity_prevented_from_trading_value; execution_price := execution_price_value; liquidity_flag := liquidity_flag_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AiqCanceledMessage.

  Module ExecutedMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      executed_shares : N;
      execution_price : N;
      liquidity_flag : list byte;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (executed_shares record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (liquidity_flag record) = 1 /\
      (match_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (executed_shares record) ++
      encode_uint 4 (execution_price record) ++
      encode_bytes 1 (liquidity_flag record) ++
      encode_uint 8 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_shares_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (execution_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (liquidity_flag_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_token := order_token_value; executed_shares := executed_shares_value; execution_price := execution_price_value; liquidity_flag := liquidity_flag_value; match_number := match_number_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutedMessage.

  Module BrokenTradeMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      match_number : N;
      broken_trade_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broken_trade_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (broken_trade_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (match_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (broken_trade_reason_value, bytes) =>
                      Some ({| timestamp := timestamp_value; order_token := order_token_value; match_number := match_number_value; broken_trade_reason := broken_trade_reason_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BrokenTradeMessage.

  Module RejectedMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      rejected_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      Datatypes.length (rejected_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_bytes 1 (rejected_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (rejected_reason_value, bytes) =>
                  Some ({| timestamp := timestamp_value; order_token := order_token_value; rejected_reason := rejected_reason_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RejectedMessage.

  Module CancelPendingMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              Some ({| timestamp := timestamp_value; order_token := order_token_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End CancelPendingMessage.

  Module CancelRejectMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              Some ({| timestamp := timestamp_value; order_token := order_token_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End CancelRejectMessage.

  Module OrderPriorityUpdateMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      price : N;
      display : list byte;
      order_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (display record) = 1 /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (display record) ++
      encode_uint 8 (order_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (display_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_reference_number_value, bytes) =>
                          Some ({| timestamp := timestamp_value; order_token := order_token_value; price := price_value; display := display_value; order_reference_number := order_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderPriorityUpdateMessage.

  Module OrderModifiedMessage.

    Record t := {
      timestamp : N;
      order_token : list byte;
      buy_sell_indicator : list byte;
      shares : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_token record) = 14 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (order_token record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (order_token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (buy_sell_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (shares_value, bytes) =>
                      Some ({| timestamp := timestamp_value; order_token := order_token_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifiedMessage.

End NtxEquitiesOrdersV42Server.
