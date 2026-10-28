From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Binary Order Entry

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
  *)

Module EdgaEquitiesBinaryOrderEntryV1014Firm.

  Module FirmMessageHeader.

    (** Message header of a packet sent by the firm *)
    Record t := {
      start_of_message : N;
      message_length : N;
      firm_message_type : N;
      matching_unit : N;
      reserved_field : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_of_message record < 256 ^ N.of_nat 2)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (firm_message_type record < 256 ^ N.of_nat 2)%N /\
      (matching_unit record < 256 ^ N.of_nat 1)%N /\
      (reserved_field record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (start_of_message record) ++
      encode_uint 2 (message_length record) ++
      encode_uint 2 (firm_message_type record) ++
      encode_uint 1 (matching_unit record) ++
      encode_uint 1 (reserved_field record) ++
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (start_of_message_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_length_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (firm_message_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (matching_unit_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_field_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (sequence_number_value, bytes) =>
                              Some ({| start_of_message := start_of_message_value; message_length := message_length_value; firm_message_type := firm_message_type_value; matching_unit := matching_unit_value; reserved_field := reserved_field_value; sequence_number := sequence_number_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End FirmMessageHeader.

  Module NewOrderUsEquitiesV1.

    (** Submission of a new order to Cboe *)
    Record t := {
      cl_ord_id : list byte;
      side : list byte;
      order_qty : N;
      clearing_firm : list byte;
      clearing_account : list byte;
      price : N;
      exec_inst : list byte;
      ord_type : list byte;
      time_in_force : list byte;
      min_qty : N;
      max_floor : N;
      symbol : list byte;
      capacity : list byte;
      routing_inst : list byte;
      account : list byte;
      display_indicator : list byte;
      discretion_amount : N;
      peg_difference : N;
      prevent_match : list byte;
      locate_reqd : list byte;
      expire_time : N;
      attributed_quote : list byte;
      ext_exec_inst : list byte;
      display_range : N;
      stop_px : N;
      rout_strategy : list byte;
      route_delivery_method : list byte;
      ex_destination : list byte;
      risk_group_id : N;
      cross_trade_flag : list byte;
      locate_broker : list byte;
      step_up_amount : N;
      cmc_sessions : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (side record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (time_in_force record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (routing_inst record) = 4 /\
      Datatypes.length (account record) = 16 /\
      Datatypes.length (display_indicator record) = 1 /\
      (discretion_amount record < 256 ^ N.of_nat 2)%N /\
      (peg_difference record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (prevent_match record) = 3 /\
      Datatypes.length (locate_reqd record) = 1 /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (attributed_quote record) = 1 /\
      Datatypes.length (ext_exec_inst record) = 1 /\
      (display_range record < 256 ^ N.of_nat 4)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (rout_strategy record) = 6 /\
      Datatypes.length (route_delivery_method record) = 3 /\
      Datatypes.length (ex_destination record) = 1 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cross_trade_flag record) = 1 /\
      Datatypes.length (locate_broker record) = 4 /\
      (step_up_amount record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cmc_sessions record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 4 (max_floor record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 4 (routing_inst record) ++
      encode_bytes 16 (account record) ++
      encode_bytes 1 (display_indicator record) ++
      encode_uint 2 (discretion_amount record) ++
      encode_uint 8 (peg_difference record) ++
      encode_bytes 3 (prevent_match record) ++
      encode_bytes 1 (locate_reqd record) ++
      encode_uint 8 (expire_time record) ++
      encode_bytes 1 (attributed_quote record) ++
      encode_bytes 1 (ext_exec_inst record) ++
      encode_uint 4 (display_range record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 6 (rout_strategy record) ++
      encode_bytes 3 (route_delivery_method record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_bytes 1 (cross_trade_flag record) ++
      encode_bytes 4 (locate_broker record) ++
      encode_uint 4 (step_up_amount record) ++
      encode_bytes 2 (cmc_sessions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_qty_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (clearing_firm_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (clearing_account_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (exec_inst_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (ord_type_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (time_in_force_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (min_qty_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (max_floor_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (symbol_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (capacity_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (routing_inst_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (account_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (display_indicator_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (discretion_amount_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (peg_difference_value, bytes) =>
                                                                              match decode_bytes 3 bytes with
                                                                              | None => None
                                                                              | Some (prevent_match_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (locate_reqd_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (expire_time_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (attributed_quote_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (ext_exec_inst_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (display_range_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (stop_px_value, bytes) =>
                                                                                                          match decode_bytes 6 bytes with
                                                                                                          | None => None
                                                                                                          | Some (rout_strategy_value, bytes) =>
                                                                                                              match decode_bytes 3 bytes with
                                                                                                              | None => None
                                                                                                              | Some (route_delivery_method_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ex_destination_value, bytes) =>
                                                                                                                      match decode_uint 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (risk_group_id_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (cross_trade_flag_value, bytes) =>
                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (locate_broker_value, bytes) =>
                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (step_up_amount_value, bytes) =>
                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (cmc_sessions_value, bytes) =>
                                                                                                                                          Some ({| cl_ord_id := cl_ord_id_value; side := side_value; order_qty := order_qty_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; price := price_value; exec_inst := exec_inst_value; ord_type := ord_type_value; time_in_force := time_in_force_value; min_qty := min_qty_value; max_floor := max_floor_value; symbol := symbol_value; capacity := capacity_value; routing_inst := routing_inst_value; account := account_value; display_indicator := display_indicator_value; discretion_amount := discretion_amount_value; peg_difference := peg_difference_value; prevent_match := prevent_match_value; locate_reqd := locate_reqd_value; expire_time := expire_time_value; attributed_quote := attributed_quote_value; ext_exec_inst := ext_exec_inst_value; display_range := display_range_value; stop_px := stop_px_value; rout_strategy := rout_strategy_value; route_delivery_method := route_delivery_method_value; ex_destination := ex_destination_value; risk_group_id := risk_group_id_value; cross_trade_flag := cross_trade_flag_value; locate_broker := locate_broker_value; step_up_amount := step_up_amount_value; cmc_sessions := cmc_sessions_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 141.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderUsEquitiesV1.

  Module NewOrderShortUsEquitiesV1.

    (** Submission of a new order to Cboe *)
    Record t := {
      cl_ord_id : list byte;
      side : list byte;
      order_qty : N;
      clearing_firm : list byte;
      clearing_account : list byte;
      price : N;
      exec_inst : list byte;
      ord_type : list byte;
      time_in_force : list byte;
      symbol : list byte;
      capacity : list byte;
      short_routing_inst : list byte;
      short_account : list byte;
      display_indicator : list byte;
      risk_group_id : N;
      locate_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (side record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (short_routing_inst record) = 1 /\
      Datatypes.length (short_account record) = 10 /\
      Datatypes.length (display_indicator record) = 1 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (locate_broker record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (short_routing_inst record) ++
      encode_bytes 10 (short_account record) ++
      encode_bytes 1 (display_indicator record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_bytes 4 (locate_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_qty_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (clearing_firm_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (clearing_account_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (exec_inst_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (ord_type_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (time_in_force_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (symbol_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (capacity_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (short_routing_inst_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (short_account_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (display_indicator_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (risk_group_id_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (locate_broker_value, bytes) =>
                                                                      Some ({| cl_ord_id := cl_ord_id_value; side := side_value; order_qty := order_qty_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; price := price_value; exec_inst := exec_inst_value; ord_type := ord_type_value; time_in_force := time_in_force_value; symbol := symbol_value; capacity := capacity_value; short_routing_inst := short_routing_inst_value; short_account := short_account_value; display_indicator := display_indicator_value; risk_group_id := risk_group_id_value; locate_broker := locate_broker_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderShortUsEquitiesV1.

  Module CancelOrderUsEquitiesV1.

    (** Request to cancel a single order *)
    Record t := {
      orig_cl_ord_id : list byte;
      clearing_firm : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (orig_cl_ord_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (clearing_firm_value, bytes) =>
              Some ({| orig_cl_ord_id := orig_cl_ord_id_value; clearing_firm := clearing_firm_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderUsEquitiesV1.

  Module ModifyOrderUsEquitiesV1.

    (** Request to modify an order *)
    Record t := {
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      clearing_firm : list byte;
      symbol : list byte;
      order_qty : N;
      price : N;
      ord_type : list byte;
      side : list byte;
      max_floor : N;
      stop_px : N;
      cancel_orig_on_reject : list byte;
      locate_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (symbol record) = 8 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cancel_orig_on_reject record) = 1 /\
      Datatypes.length (locate_broker record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 1 (cancel_orig_on_reject record) ++
      encode_bytes 4 (locate_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (orig_cl_ord_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (max_floor_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (stop_px_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cancel_orig_on_reject_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (locate_broker_value, bytes) =>
                                                      Some ({| cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; clearing_firm := clearing_firm_value; symbol := symbol_value; order_qty := order_qty_value; price := price_value; ord_type := ord_type_value; side := side_value; max_floor := max_floor_value; stop_px := stop_px_value; cancel_orig_on_reject := cancel_orig_on_reject_value; locate_broker := locate_broker_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 83.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderUsEquitiesV1.

  Module ResetRiskUsEquitiesV1.

    (** Reset or release Firm, Symbol, or Risk Group ID level lockout conditions resulting from risk profile trips or self-imposed lockouts issued via Purge Orders messages *)
    Record t := {
      risk_status_id : list byte;
      risk_reset : list byte;
      clearing_firm : list byte;
      symbol : list byte;
      target_matching_unit : N;
      risk_group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (risk_status_id record) = 16 /\
      Datatypes.length (risk_reset record) = 8 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (symbol record) = 8 /\
      (target_matching_unit record < 256 ^ N.of_nat 1)%N /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (risk_status_id record) ++
      encode_bytes 8 (risk_reset record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 1 (target_matching_unit record) ++
      encode_uint 2 (risk_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (risk_status_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (risk_reset_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (target_matching_unit_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (risk_group_id_value, bytes) =>
                              Some ({| risk_status_id := risk_status_id_value; risk_reset := risk_reset_value; clearing_firm := clearing_firm_value; symbol := symbol_value; target_matching_unit := target_matching_unit_value; risk_group_id := risk_group_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResetRiskUsEquitiesV1.

End EdgaEquitiesBinaryOrderEntryV1014Firm.
