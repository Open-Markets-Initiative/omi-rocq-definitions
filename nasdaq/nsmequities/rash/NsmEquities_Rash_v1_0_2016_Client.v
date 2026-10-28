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

Module NsmEquitiesRashV102016Client.

  Module ClientPacketHeader.

    (** Packet header of a packet sent by the client *)
    Record t := {
      packet_length : N;
      client_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (client_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (client_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (client_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; client_packet_type := client_packet_type_value |}, bytes)
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

  End ClientPacketHeader.

  Module LoginRequestPacket.

    (** The SoupBinTCP client must send a Login Request Packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      username : list byte;
      password : list byte;
      requested_session : list byte;
      requested_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 20 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (requested_session_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequestPacket.

  Module EnterOrderMessage.

    (** The Enter Order Message lets you enter a new order. Each new order must have a Token that is unique to the day and that logical RASH Port account. If you send a valid order, you should receive an Accepted Order Message. *)
    Record t := {
      order_token_client_order_id : list byte;
      side : list byte;
      shares_order_qty : list byte;
      stock_symbol : list byte;
      price : list byte;
      time_in_force : list byte;
      firm_client_id : list byte;
      display : list byte;
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
      customer_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (shares_order_qty record) = 6 /\
      Datatypes.length (stock_symbol record) = 6 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (time_in_force record) = 5 /\
      Datatypes.length (firm_client_id record) = 4 /\
      Datatypes.length (display record) = 1 /\
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
      Datatypes.length (customer_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (shares_order_qty record) ++
      encode_bytes 6 (stock_symbol record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 5 (time_in_force record) ++
      encode_bytes 4 (firm_client_id record) ++
      encode_bytes 1 (display record) ++
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
      encode_bytes 1 (customer_type record).

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
                  match decode_bytes 6 bytes with
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
                                                                                          | Some (customer_type_value, bytes) =>
                                                                                              Some ({| order_token_client_order_id := order_token_client_order_id_value; side := side_value; shares_order_qty := shares_order_qty_value; stock_symbol := stock_symbol_value; price := price_value; time_in_force := time_in_force_value; firm_client_id := firm_client_id_value; display := display_value; min_qty := min_qty_value; max_floor := max_floor_value; peg_type := peg_type_value; peg_difference_sign := peg_difference_sign_value; peg_difference := peg_difference_value; discretion_price := discretion_price_value; discretion_peg_type := discretion_peg_type_value; discretion_peg_difference_sign := discretion_peg_difference_sign_value; discretion_peg_difference := discretion_peg_difference_value; capacity_rule_80_a_indicator := capacity_rule_80_a_indicator_value; random_reserve := random_reserve_value; route_dest_exec_broker := route_dest_exec_broker_value; cust_terminal_id_sender_sub_id := cust_terminal_id_sender_sub_id_value; customer_type := customer_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 137.
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

  End EnterOrderMessage.

  Module EnterOrderMessageWithCrossFunctionality.

    (** Enters orders in much the same way as the Enter Order Message, with a few additional fields. Notably, the Cross Type Flag allows you to specify that an order begins participation in a cross. *)
    Record t := {
      order_token_client_order_id : list byte;
      side : list byte;
      shares_order_qty : list byte;
      stock_symbol : list byte;
      price : list byte;
      time_in_force : list byte;
      firm_client_id : list byte;
      display : list byte;
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
      customer_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (shares_order_qty record) = 6 /\
      Datatypes.length (stock_symbol record) = 6 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (time_in_force record) = 5 /\
      Datatypes.length (firm_client_id record) = 4 /\
      Datatypes.length (display record) = 1 /\
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
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (customer_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (shares_order_qty record) ++
      encode_bytes 6 (stock_symbol record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 5 (time_in_force record) ++
      encode_bytes 4 (firm_client_id record) ++
      encode_bytes 1 (display record) ++
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
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (customer_type record).

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
                  match decode_bytes 6 bytes with
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
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (customer_type_value, bytes) =>
                                                                                                      Some ({| order_token_client_order_id := order_token_client_order_id_value; side := side_value; shares_order_qty := shares_order_qty_value; stock_symbol := stock_symbol_value; price := price_value; time_in_force := time_in_force_value; firm_client_id := firm_client_id_value; display := display_value; min_qty := min_qty_value; max_floor := max_floor_value; peg_type := peg_type_value; peg_difference_sign := peg_difference_sign_value; peg_difference := peg_difference_value; discretion_price := discretion_price_value; discretion_peg_type := discretion_peg_type_value; discretion_peg_difference_sign := discretion_peg_difference_sign_value; discretion_peg_difference := discretion_peg_difference_value; capacity_rule_80_a_indicator := capacity_rule_80_a_indicator_value; random_reserve := random_reserve_value; route_dest_exec_broker := route_dest_exec_broker_value; cust_terminal_id_sender_sub_id := cust_terminal_id_sender_sub_id_value; inter_market_sweep_eligibility := inter_market_sweep_eligibility_value; cross_type := cross_type_value; customer_type := customer_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 139.
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

  End EnterOrderMessageWithCrossFunctionality.

  Module CancelOrderMessage.

    (** Requests that an order be canceled. A Shares field of zero cancels the entire balance of the order; otherwise Shares is the new intended order size. *)
    Record t := {
      order_token_client_order_id : list byte;
      shares : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_token_client_order_id record) = 14 /\
      Datatypes.length (shares record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (order_token_client_order_id record) ++
      encode_bytes 6 (shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (order_token_client_order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (shares_value, bytes) =>
              Some ({| order_token_client_order_id := order_token_client_order_id_value; shares := shares_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End CancelOrderMessage.

End NsmEquitiesRashV102016Client.
