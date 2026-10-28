From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Rash

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

Module NsmEquitiesRashV11Server.

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

  Module SequencedMessageHeader.

    (** Time Stamp and type carried ahead of every RASH outbound sequenced message *)
    Record t := {
      timestamp : list byte;
      sequenced_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (sequenced_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (timestamp record) ++
      encode_bytes 1 (sequenced_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sequenced_message_type_value, bytes) =>
              Some ({| timestamp := timestamp_value; sequenced_message_type := sequenced_message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SequencedMessageHeader.

  Module SystemEventMessage.

    (** System Event Messages signal events that affect the entire system. *)
    Record t := {
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (event_code_value, bytes) =>
          Some ({| event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module AcceptedOrderMessage.

    (** An Accepted Order Message acknowledges the receipt of a valid Enter Order Message. The data fields from the Enter Order Message are echoed back; the accepted values may differ from the entered values for some fields. *)
    Record t := {
      order_token_client_order_id : list byte;
      side : list byte;
      shares_order_qty : list byte;
      stock_symbol : list byte;
      price : list byte;
      time_in_force : list byte;
      firm_client_id : list byte;
      display : list byte;
      order_reference_number : list byte;
      min_qty : list byte;
      max_floor : list byte;
      peg_type : list byte;
      peg_difference_sign : list byte;
      peg_difference : list byte;
      discretion_price : list byte;
      discretion_peg_type : list byte;
      discretion_peg_difference_sign : list byte;
      discretion_peg_difference : list byte;
      capacity_rule_80_a_indicator : list byte;
      random_reserve : list byte;
      route_dest_exec_broker : list byte;
      cust_terminal_id_sender_sub_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (shares_order_qty record) = 6 /\
      Datatypes.length (stock_symbol record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (time_in_force record) = 5 /\
      Datatypes.length (firm_client_id record) = 4 /\
      Datatypes.length (display record) = 1 /\
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (min_qty record) = 6 /\
      Datatypes.length (max_floor record) = 6 /\
      Datatypes.length (peg_type record) = 1 /\
      Datatypes.length (peg_difference_sign record) = 1 /\
      Datatypes.length (peg_difference record) = 10 /\
      Datatypes.length (discretion_price record) = 10 /\
      Datatypes.length (discretion_peg_type record) = 1 /\
      Datatypes.length (discretion_peg_difference_sign record) = 1 /\
      Datatypes.length (discretion_peg_difference record) = 10 /\
      Datatypes.length (capacity_rule_80_a_indicator record) = 1 /\
      Datatypes.length (random_reserve record) = 6 /\
      Datatypes.length (route_dest_exec_broker record) = 4 /\
      Datatypes.length (cust_terminal_id_sender_sub_id record) = 32.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (shares_order_qty record) ++
      encode_bytes 8 (stock_symbol record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 5 (time_in_force record) ++
      encode_bytes 4 (firm_client_id record) ++
      encode_bytes 1 (display record) ++
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 6 (min_qty record) ++
      encode_bytes 6 (max_floor record) ++
      encode_bytes 1 (peg_type record) ++
      encode_bytes 1 (peg_difference_sign record) ++
      encode_bytes 10 (peg_difference record) ++
      encode_bytes 10 (discretion_price record) ++
      encode_bytes 1 (discretion_peg_type record) ++
      encode_bytes 1 (discretion_peg_difference_sign record) ++
      encode_bytes 10 (discretion_peg_difference record) ++
      encode_bytes 1 (capacity_rule_80_a_indicator record) ++
      encode_bytes 6 (random_reserve record) ++
      encode_bytes 4 (route_dest_exec_broker record) ++
      encode_bytes 32 (cust_terminal_id_sender_sub_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_order_qty_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_symbol_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (time_in_force_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (firm_client_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (display_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (order_reference_number_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (min_qty_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (max_floor_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (peg_type_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (peg_difference_sign_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (peg_difference_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (discretion_price_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (discretion_peg_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (discretion_peg_difference_sign_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (discretion_peg_difference_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (capacity_rule_80_a_indicator_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (random_reserve_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (route_dest_exec_broker_value, bytes) =>
                                                                                          match decode_bytes 32 bytes with
                                                                                          | None => None
                                                                                          | Some (cust_terminal_id_sender_sub_id_value, bytes) =>
                                                                                              Some ({| order_token_client_order_id := order_token_client_order_id_value; side := side_value; shares_order_qty := shares_order_qty_value; stock_symbol := stock_symbol_value; price := price_value; time_in_force := time_in_force_value; firm_client_id := firm_client_id_value; display := display_value; order_reference_number := order_reference_number_value; min_qty := min_qty_value; max_floor := max_floor_value; peg_type := peg_type_value; peg_difference_sign := peg_difference_sign_value; peg_difference := peg_difference_value; discretion_price := discretion_price_value; discretion_peg_type := discretion_peg_type_value; discretion_peg_difference_sign := discretion_peg_difference_sign_value; discretion_peg_difference := discretion_peg_difference_value; capacity_rule_80_a_indicator := capacity_rule_80_a_indicator_value; random_reserve := random_reserve_value; route_dest_exec_broker := route_dest_exec_broker_value; cust_terminal_id_sender_sub_id := cust_terminal_id_sender_sub_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 147.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AcceptedOrderMessage.

  Module AcceptedOrderMessageWithCrossFunctionality.

    (** Similar to the regular Accepted Order Message, with the additional information provided upon order entry using the Enter Order Message with Cross Functionality. *)
    Record t := {
      order_token_client_order_id : list byte;
      side : list byte;
      shares_order_qty : list byte;
      stock_symbol : list byte;
      price : list byte;
      time_in_force : list byte;
      firm_client_id : list byte;
      display : list byte;
      order_reference_number : list byte;
      min_qty : list byte;
      max_floor : list byte;
      peg_type : list byte;
      peg_difference_sign : list byte;
      peg_difference : list byte;
      discretion_price : list byte;
      discretion_peg_type : list byte;
      discretion_peg_difference_sign : list byte;
      discretion_peg_difference : list byte;
      capacity_rule_80_a_indicator : list byte;
      random_reserve : list byte;
      route_dest_exec_broker : list byte;
      cust_terminal_id_sender_sub_id : list byte;
      inter_market_sweep_eligibility : list byte;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (shares_order_qty record) = 6 /\
      Datatypes.length (stock_symbol record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (time_in_force record) = 5 /\
      Datatypes.length (firm_client_id record) = 4 /\
      Datatypes.length (display record) = 1 /\
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (min_qty record) = 6 /\
      Datatypes.length (max_floor record) = 6 /\
      Datatypes.length (peg_type record) = 1 /\
      Datatypes.length (peg_difference_sign record) = 1 /\
      Datatypes.length (peg_difference record) = 10 /\
      Datatypes.length (discretion_price record) = 10 /\
      Datatypes.length (discretion_peg_type record) = 1 /\
      Datatypes.length (discretion_peg_difference_sign record) = 1 /\
      Datatypes.length (discretion_peg_difference record) = 10 /\
      Datatypes.length (capacity_rule_80_a_indicator record) = 1 /\
      Datatypes.length (random_reserve record) = 6 /\
      Datatypes.length (route_dest_exec_broker record) = 4 /\
      Datatypes.length (cust_terminal_id_sender_sub_id record) = 32 /\
      Datatypes.length (inter_market_sweep_eligibility record) = 1 /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (shares_order_qty record) ++
      encode_bytes 8 (stock_symbol record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 5 (time_in_force record) ++
      encode_bytes 4 (firm_client_id record) ++
      encode_bytes 1 (display record) ++
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 6 (min_qty record) ++
      encode_bytes 6 (max_floor record) ++
      encode_bytes 1 (peg_type record) ++
      encode_bytes 1 (peg_difference_sign record) ++
      encode_bytes 10 (peg_difference record) ++
      encode_bytes 10 (discretion_price record) ++
      encode_bytes 1 (discretion_peg_type record) ++
      encode_bytes 1 (discretion_peg_difference_sign record) ++
      encode_bytes 10 (discretion_peg_difference record) ++
      encode_bytes 1 (capacity_rule_80_a_indicator record) ++
      encode_bytes 6 (random_reserve record) ++
      encode_bytes 4 (route_dest_exec_broker record) ++
      encode_bytes 32 (cust_terminal_id_sender_sub_id record) ++
      encode_bytes 1 (inter_market_sweep_eligibility record) ++
      encode_bytes 1 (cross_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_order_qty_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_symbol_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (time_in_force_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (firm_client_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (display_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (order_reference_number_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (min_qty_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (max_floor_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (peg_type_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (peg_difference_sign_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (peg_difference_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (discretion_price_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (discretion_peg_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (discretion_peg_difference_sign_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (discretion_peg_difference_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (capacity_rule_80_a_indicator_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (random_reserve_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (route_dest_exec_broker_value, bytes) =>
                                                                                          match decode_bytes 32 bytes with
                                                                                          | None => None
                                                                                          | Some (cust_terminal_id_sender_sub_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (inter_market_sweep_eligibility_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (cross_type_value, bytes) =>
                                                                                                      Some ({| order_token_client_order_id := order_token_client_order_id_value; side := side_value; shares_order_qty := shares_order_qty_value; stock_symbol := stock_symbol_value; price := price_value; time_in_force := time_in_force_value; firm_client_id := firm_client_id_value; display := display_value; order_reference_number := order_reference_number_value; min_qty := min_qty_value; max_floor := max_floor_value; peg_type := peg_type_value; peg_difference_sign := peg_difference_sign_value; peg_difference := peg_difference_value; discretion_price := discretion_price_value; discretion_peg_type := discretion_peg_type_value; discretion_peg_difference_sign := discretion_peg_difference_sign_value; discretion_peg_difference := discretion_peg_difference_value; capacity_rule_80_a_indicator := capacity_rule_80_a_indicator_value; random_reserve := random_reserve_value; route_dest_exec_broker := route_dest_exec_broker_value; cust_terminal_id_sender_sub_id := cust_terminal_id_sender_sub_id_value; inter_market_sweep_eligibility := inter_market_sweep_eligibility_value; cross_type := cross_type_value |}, bytes)
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
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 149.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 bound_23]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AcceptedOrderMessageWithCrossFunctionality.

  Module CanceledOrderMessage.

    (** A Canceled Order Message informs you that an order has been reduced or canceled. Canceled shares reflect the number of shares that are out. *)
    Record t := {
      order_token_client_order_id : list byte;
      shares : list byte;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (shares record) = 6 /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 6 (shares record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (shares_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (cancel_reason_value, bytes) =>
                  Some ({| order_token_client_order_id := order_token_client_order_id_value; shares := shares_value; cancel_reason := cancel_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CanceledOrderMessage.

  Module RejectedOrderMessage.

    (** A Rejected Order Message may be sent in response to an Enter Order Message if the order cannot be accepted at this time. The Token of a rejected order cannot be re-used. *)
    Record t := {
      order_token_client_order_id : list byte;
      reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (reject_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 1 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reject_reason_value, bytes) =>
              Some ({| order_token_client_order_id := order_token_client_order_id_value; reject_reason := reject_reason_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End RejectedOrderMessage.

  Module ExecutedOrderMessage.

    (** An Executed Order Message informs you that all or part of an order has been executed. *)
    Record t := {
      order_token_client_order_id : list byte;
      shares : list byte;
      price : list byte;
      liquidity : list byte;
      match_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (shares record) = 6 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (liquidity record) = 1 /\
      Datatypes.length (match_number record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 6 (shares record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 1 (liquidity record) ++
      encode_bytes 9 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (shares_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (liquidity_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          Some ({| order_token_client_order_id := order_token_client_order_id_value; shares := shares_value; price := price_value; liquidity := liquidity_value; match_number := match_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutedOrderMessage.

  Module BrokenTradeMessage.

    (** A Broken Trade Message informs you that an execution has been broken. The trade is no longer good and will not clear. *)
    Record t := {
      order_token : list byte;
      match_number : list byte;
      broken_trade_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token record) = 14 /\
      Datatypes.length (match_number record) = 9 /\
      Datatypes.length (broken_trade_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token record) ++
      encode_bytes 9 (match_number record) ++
      encode_bytes 1 (broken_trade_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (match_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (broken_trade_reason_value, bytes) =>
                  Some ({| order_token := order_token_value; match_number := match_number_value; broken_trade_reason := broken_trade_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BrokenTradeMessage.

  Module ExecutedWithReferencePriceMessage.

    (** Informs you that all or part of an order has been executed, with the reference price associated with the execution. *)
    Record t := {
      order_token_client_order_id : list byte;
      shares : list byte;
      price : list byte;
      liquidity : list byte;
      match_number : list byte;
      reference_price : list byte;
      reference_price_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (shares record) = 6 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (liquidity record) = 1 /\
      Datatypes.length (match_number record) = 9 /\
      Datatypes.length (reference_price record) = 10 /\
      Datatypes.length (reference_price_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 6 (shares record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 1 (liquidity record) ++
      encode_bytes 9 (match_number record) ++
      encode_bytes 10 (reference_price record) ++
      encode_bytes 1 (reference_price_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (shares_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (liquidity_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (reference_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (reference_price_type_value, bytes) =>
                                  Some ({| order_token_client_order_id := order_token_client_order_id_value; shares := shares_value; price := price_value; liquidity := liquidity_value; match_number := match_number_value; reference_price := reference_price_value; reference_price_type := reference_price_type_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutedWithReferencePriceMessage.

  Module TradeCorrectionMessage.

    (** A Trade Correction Message informs you that there has been a change to an execution. *)
    Record t := {
      order_token_client_order_id : list byte;
      shares : list byte;
      price : list byte;
      liquidity : list byte;
      match_number : list byte;
      trade_correction_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (shares record) = 6 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (liquidity record) = 1 /\
      Datatypes.length (match_number record) = 9 /\
      Datatypes.length (trade_correction_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 6 (shares record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 1 (liquidity record) ++
      encode_bytes 9 (match_number record) ++
      encode_bytes 1 (trade_correction_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (shares_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (liquidity_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (trade_correction_reason_value, bytes) =>
                              Some ({| order_token_client_order_id := order_token_client_order_id_value; shares := shares_value; price := price_value; liquidity := liquidity_value; match_number := match_number_value; trade_correction_reason := trade_correction_reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

End NsmEquitiesRashV11Server.
