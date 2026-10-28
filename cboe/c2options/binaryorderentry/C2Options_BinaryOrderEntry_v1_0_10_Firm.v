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

Module C2OptionsBinaryOrderEntryV1010Firm.

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

  Module PreventMatch.

    Record t := {
      mtp_modifier : list byte;
      unique_id_level : list byte;
      trading_group_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mtp_modifier record) = 1 /\
      Datatypes.length (unique_id_level record) = 1 /\
      Datatypes.length (trading_group_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (mtp_modifier record) ++
      encode_bytes 1 (unique_id_level record) ++
      encode_bytes 1 (trading_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (mtp_modifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (unique_id_level_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_group_id_value, bytes) =>
                  Some ({| mtp_modifier := mtp_modifier_value; unique_id_level := unique_id_level_value; trading_group_id := trading_group_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End PreventMatch.

  Module NewOrderMessage.

    (** Submission of a new simple (single leg) order to Cboe *)
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
      prevent_match : PreventMatch.t;
      expire_time : N;
      maturity_date : N;
      strike_price : N;
      put_or_call : list byte;
      open_close : list byte;
      cmta_number : N;
      target_party_id : list byte;
      session_eligibility : list byte;
      attributed_quote : list byte;
      display_range : N;
      stop_px : N;
      rout_strategy : list byte;
      route_delivery_method : list byte;
      ex_destination : list byte;
      auction_id : N;
      routing_firm_id : list byte;
      custom_group_id : N;
      clearing_optional_data : list byte;
      client_id_attr : list byte;
      frequent_trader_id : list byte;
      compression : list byte;
      floor_destination : list byte;
      floor_routing_inst : list byte;
      order_origin : list byte;
      order_router_subsidy : list byte;
      price_type : list byte;
      held : list byte;
      scratch_pad : N;
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
      PreventMatch.bounded (prevent_match record) /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (put_or_call record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      (cmta_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (target_party_id record) = 4 /\
      Datatypes.length (session_eligibility record) = 1 /\
      Datatypes.length (attributed_quote record) = 1 /\
      (display_range record < 256 ^ N.of_nat 4)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (rout_strategy record) = 6 /\
      Datatypes.length (route_delivery_method record) = 3 /\
      Datatypes.length (ex_destination record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (routing_firm_id record) = 4 /\
      (custom_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (clearing_optional_data record) = 16 /\
      Datatypes.length (client_id_attr record) = 4 /\
      Datatypes.length (frequent_trader_id record) = 6 /\
      Datatypes.length (compression record) = 1 /\
      Datatypes.length (floor_destination record) = 4 /\
      Datatypes.length (floor_routing_inst record) = 1 /\
      Datatypes.length (order_origin record) = 3 /\
      Datatypes.length (order_router_subsidy record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (held record) = 1 /\
      (scratch_pad record < 256 ^ N.of_nat 2)%N.

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
      PreventMatch.encode (prevent_match record) ++
      encode_uint 8 (expire_time record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_bytes 1 (open_close record) ++
      encode_uint 4 (cmta_number record) ++
      encode_bytes 4 (target_party_id record) ++
      encode_bytes 1 (session_eligibility record) ++
      encode_bytes 1 (attributed_quote record) ++
      encode_uint 4 (display_range record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 6 (rout_strategy record) ++
      encode_bytes 3 (route_delivery_method record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_uint 8 (auction_id record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_uint 2 (custom_group_id record) ++
      encode_bytes 16 (clearing_optional_data record) ++
      encode_bytes 4 (client_id_attr record) ++
      encode_bytes 6 (frequent_trader_id record) ++
      encode_bytes 1 (compression record) ++
      encode_bytes 4 (floor_destination record) ++
      encode_bytes 1 (floor_routing_inst record) ++
      encode_bytes 3 (order_origin record) ++
      encode_bytes 1 (order_router_subsidy record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (held record) ++
      encode_uint 2 (scratch_pad record).

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
                                                                      match PreventMatch.decode bytes with
                                                                      | None => None
                                                                      | Some (prevent_match_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (expire_time_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (maturity_date_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (strike_price_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (put_or_call_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (open_close_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (cmta_number_value, bytes) =>
                                                                                                  match decode_bytes 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (target_party_id_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (session_eligibility_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (attributed_quote_value, bytes) =>
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
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (auction_id_value, bytes) =>
                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (routing_firm_id_value, bytes) =>
                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (custom_group_id_value, bytes) =>
                                                                                                                                              match decode_bytes 16 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (clearing_optional_data_value, bytes) =>
                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (client_id_attr_value, bytes) =>
                                                                                                                                                      match decode_bytes 6 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (frequent_trader_id_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (compression_value, bytes) =>
                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (floor_destination_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (floor_routing_inst_value, bytes) =>
                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (order_origin_value, bytes) =>
                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (order_router_subsidy_value, bytes) =>
                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (price_type_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (held_value, bytes) =>
                                                                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (scratch_pad_value, bytes) =>
                                                                                                                                                                                          Some ({| cl_ord_id := cl_ord_id_value; side := side_value; order_qty := order_qty_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; price := price_value; exec_inst := exec_inst_value; ord_type := ord_type_value; time_in_force := time_in_force_value; min_qty := min_qty_value; max_floor := max_floor_value; symbol := symbol_value; capacity := capacity_value; routing_inst := routing_inst_value; account := account_value; display_indicator := display_indicator_value; prevent_match := prevent_match_value; expire_time := expire_time_value; maturity_date := maturity_date_value; strike_price := strike_price_value; put_or_call := put_or_call_value; open_close := open_close_value; cmta_number := cmta_number_value; target_party_id := target_party_id_value; session_eligibility := session_eligibility_value; attributed_quote := attributed_quote_value; display_range := display_range_value; stop_px := stop_px_value; rout_strategy := rout_strategy_value; route_delivery_method := route_delivery_method_value; ex_destination := ex_destination_value; auction_id := auction_id_value; routing_firm_id := routing_firm_id_value; custom_group_id := custom_group_id_value; clearing_optional_data := clearing_optional_data_value; client_id_attr := client_id_attr_value; frequent_trader_id := frequent_trader_id_value; compression := compression_value; floor_destination := floor_destination_value; floor_routing_inst := floor_routing_inst_value; order_origin := order_origin_value; order_router_subsidy := order_router_subsidy_value; price_type := price_type_value; held := held_value; scratch_pad := scratch_pad_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 193.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !PreventMatch.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 bound_44]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite PreventMatch.decode_encode by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply PreventMatch.eq_dec]. Defined.

  End NewOrderMessage.

  Module PreventMatch2.

    Record t := {
      mtp_modifier : list byte;
      unique_id_level : list byte;
      trading_group_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mtp_modifier record) = 1 /\
      Datatypes.length (unique_id_level record) = 1 /\
      Datatypes.length (trading_group_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (mtp_modifier record) ++
      encode_bytes 1 (unique_id_level record) ++
      encode_bytes 1 (trading_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (mtp_modifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (unique_id_level_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_group_id_value, bytes) =>
                  Some ({| mtp_modifier := mtp_modifier_value; unique_id_level := unique_id_level_value; trading_group_id := trading_group_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End PreventMatch2.

  Module NewOrderShortMessage.

    (** Submission of a new simple (single leg) order to Cboe *)
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
      prevent_match : PreventMatch2.t;
      open_close : list byte;
      cmta_number : N;
      session_eligibility : list byte;
      attributed_quote : list byte;
      rout_strategy : list byte;
      ex_destination : list byte;
      auction_id : N;
      custom_group_id : N;
      frequent_trader_id : list byte;
      scratch_pad : N;
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
      PreventMatch2.bounded (prevent_match record) /\
      Datatypes.length (open_close record) = 1 /\
      (cmta_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (session_eligibility record) = 1 /\
      Datatypes.length (attributed_quote record) = 1 /\
      Datatypes.length (rout_strategy record) = 6 /\
      Datatypes.length (ex_destination record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      (custom_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (frequent_trader_id record) = 6 /\
      (scratch_pad record < 256 ^ N.of_nat 2)%N.

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
      PreventMatch2.encode (prevent_match record) ++
      encode_bytes 1 (open_close record) ++
      encode_uint 4 (cmta_number record) ++
      encode_bytes 1 (session_eligibility record) ++
      encode_bytes 1 (attributed_quote record) ++
      encode_bytes 6 (rout_strategy record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_uint 8 (auction_id record) ++
      encode_uint 2 (custom_group_id record) ++
      encode_bytes 6 (frequent_trader_id record) ++
      encode_uint 2 (scratch_pad record).

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
                                                                      match PreventMatch2.decode bytes with
                                                                      | None => None
                                                                      | Some (prevent_match_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (open_close_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (cmta_number_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (session_eligibility_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (attributed_quote_value, bytes) =>
                                                                                          match decode_bytes 6 bytes with
                                                                                          | None => None
                                                                                          | Some (rout_strategy_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (ex_destination_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (auction_id_value, bytes) =>
                                                                                                      match decode_uint 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (custom_group_id_value, bytes) =>
                                                                                                          match decode_bytes 6 bytes with
                                                                                                          | None => None
                                                                                                          | Some (frequent_trader_id_value, bytes) =>
                                                                                                              match decode_uint 2 bytes with
                                                                                                              | None => None
                                                                                                              | Some (scratch_pad_value, bytes) =>
                                                                                                                  Some ({| cl_ord_id := cl_ord_id_value; side := side_value; order_qty := order_qty_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; price := price_value; exec_inst := exec_inst_value; ord_type := ord_type_value; time_in_force := time_in_force_value; min_qty := min_qty_value; max_floor := max_floor_value; symbol := symbol_value; capacity := capacity_value; routing_inst := routing_inst_value; account := account_value; display_indicator := display_indicator_value; prevent_match := prevent_match_value; open_close := open_close_value; cmta_number := cmta_number_value; session_eligibility := session_eligibility_value; attributed_quote := attributed_quote_value; rout_strategy := rout_strategy_value; ex_destination := ex_destination_value; auction_id := auction_id_value; custom_group_id := custom_group_id_value; frequent_trader_id := frequent_trader_id_value; scratch_pad := scratch_pad_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 117.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !PreventMatch2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite PreventMatch2.decode_encode by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply PreventMatch2.eq_dec]. Defined.

  End NewOrderShortMessage.

  Module PreventMatch3.

    Record t := {
      mtp_modifier : list byte;
      unique_id_level : list byte;
      trading_group_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mtp_modifier record) = 1 /\
      Datatypes.length (unique_id_level record) = 1 /\
      Datatypes.length (trading_group_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (mtp_modifier record) ++
      encode_bytes 1 (unique_id_level record) ++
      encode_bytes 1 (trading_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (mtp_modifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (unique_id_level_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_group_id_value, bytes) =>
                  Some ({| mtp_modifier := mtp_modifier_value; unique_id_level := unique_id_level_value; trading_group_id := trading_group_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End PreventMatch3.

  Module PreventMatch4.

    Record t := {
      mtp_modifier : list byte;
      unique_id_level : list byte;
      trading_group_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mtp_modifier record) = 1 /\
      Datatypes.length (unique_id_level record) = 1 /\
      Datatypes.length (trading_group_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (mtp_modifier record) ++
      encode_bytes 1 (unique_id_level record) ++
      encode_bytes 1 (trading_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (mtp_modifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (unique_id_level_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_group_id_value, bytes) =>
                  Some ({| mtp_modifier := mtp_modifier_value; unique_id_level := unique_id_level_value; trading_group_id := trading_group_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End PreventMatch4.

  Module CancelOrderMessage.

    (** Request to cancel a single order *)
    Record t := {
      orig_cl_ord_id : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      scratch_pad : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      (scratch_pad record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_uint 2 (scratch_pad record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (orig_cl_ord_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (clearing_firm_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (routing_firm_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (scratch_pad_value, bytes) =>
                      Some ({| orig_cl_ord_id := orig_cl_ord_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; scratch_pad := scratch_pad_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderMessage.

  Module MassCancelInst.

    Record t := {
      clearing_firm_filter : list byte;
      acknowledgement_style : list byte;
      lockout_instruction : list byte;
      instrument_type_filter : list byte;
      gtc_order_filter : list byte;
      instruction_details : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_firm_filter record) = 1 /\
      Datatypes.length (acknowledgement_style record) = 1 /\
      Datatypes.length (lockout_instruction record) = 1 /\
      Datatypes.length (instrument_type_filter record) = 1 /\
      Datatypes.length (gtc_order_filter record) = 1 /\
      Datatypes.length (instruction_details record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (clearing_firm_filter record) ++
      encode_bytes 1 (acknowledgement_style record) ++
      encode_bytes 1 (lockout_instruction record) ++
      encode_bytes 1 (instrument_type_filter record) ++
      encode_bytes 1 (gtc_order_filter record) ++
      encode_bytes 3 (instruction_details record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (clearing_firm_filter_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (acknowledgement_style_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (lockout_instruction_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (instrument_type_filter_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (gtc_order_filter_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (instruction_details_value, bytes) =>
                              Some ({| clearing_firm_filter := clearing_firm_filter_value; acknowledgement_style := acknowledgement_style_value; lockout_instruction := lockout_instruction_value; instrument_type_filter := instrument_type_filter_value; gtc_order_filter := gtc_order_filter_value; instruction_details := instruction_details_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End MassCancelInst.

  Module MassCancelOrderMessage.

    (** MassCancelOrderMessage *)
    Record t := {
      mass_cancel_id : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      risk_root : list byte;
      mass_cancel_inst : MassCancelInst.t;
      send_time : N;
      scratch_pad : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mass_cancel_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (risk_root record) = 6 /\
      MassCancelInst.bounded (mass_cancel_inst record) /\
      (send_time record < 256 ^ N.of_nat 8)%N /\
      (scratch_pad record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (mass_cancel_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 6 (risk_root record) ++
      MassCancelInst.encode (mass_cancel_inst record) ++
      encode_uint 8 (send_time record) ++
      encode_uint 2 (scratch_pad record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (mass_cancel_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (clearing_firm_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (routing_firm_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (risk_root_value, bytes) =>
                      match MassCancelInst.decode bytes with
                      | None => None
                      | Some (mass_cancel_inst_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (send_time_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (scratch_pad_value, bytes) =>
                                  Some ({| mass_cancel_id := mass_cancel_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; risk_root := risk_root_value; mass_cancel_inst := mass_cancel_inst_value; send_time := send_time_value; scratch_pad := scratch_pad_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !MassCancelInst.encode_length, !encode_uint_length. reflexivity.
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
      rewrite MassCancelInst.decode_encode by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MassCancelInst.eq_dec]. Defined.

  End MassCancelOrderMessage.

  Module ModifyOrderMessage.

    (** Request to modify an order *)
    Record t := {
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      order_qty : N;
      price : N;
      ord_type : list byte;
      max_floor : N;
      stop_px : N;
      cancel_orig_on_reject : list byte;
      reserved : list byte;
      scratch_pad : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cancel_orig_on_reject record) = 1 /\
      Datatypes.length (reserved record) = 41 /\
      (scratch_pad record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 1 (cancel_orig_on_reject record) ++
      encode_bytes 41 (reserved record) ++
      encode_uint 2 (scratch_pad record).

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
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (routing_firm_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (max_floor_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (stop_px_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cancel_orig_on_reject_value, bytes) =>
                                              match decode_bytes 41 bytes with
                                              | None => None
                                              | Some (reserved_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (scratch_pad_value, bytes) =>
                                                      Some ({| cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; order_qty := order_qty_value; price := price_value; ord_type := ord_type_value; max_floor := max_floor_value; stop_px := stop_px_value; cancel_orig_on_reject := cancel_orig_on_reject_value; reserved := reserved_value; scratch_pad := scratch_pad_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 117.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderMessage.

  Module MassCancelInst2.

    Record t := {
      clearing_firm_filter : list byte;
      acknowledgement_style : list byte;
      lockout_instruction : list byte;
      instrument_type_filter : list byte;
      gtc_order_filter : list byte;
      instruction_details : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_firm_filter record) = 1 /\
      Datatypes.length (acknowledgement_style record) = 1 /\
      Datatypes.length (lockout_instruction record) = 1 /\
      Datatypes.length (instrument_type_filter record) = 1 /\
      Datatypes.length (gtc_order_filter record) = 1 /\
      Datatypes.length (instruction_details record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (clearing_firm_filter record) ++
      encode_bytes 1 (acknowledgement_style record) ++
      encode_bytes 1 (lockout_instruction record) ++
      encode_bytes 1 (instrument_type_filter record) ++
      encode_bytes 1 (gtc_order_filter record) ++
      encode_bytes 3 (instruction_details record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (clearing_firm_filter_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (acknowledgement_style_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (lockout_instruction_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (instrument_type_filter_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (gtc_order_filter_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (instruction_details_value, bytes) =>
                              Some ({| clearing_firm_filter := clearing_firm_filter_value; acknowledgement_style := acknowledgement_style_value; lockout_instruction := lockout_instruction_value; instrument_type_filter := instrument_type_filter_value; gtc_order_filter := gtc_order_filter_value; instruction_details := instruction_details_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End MassCancelInst2.

  Module ResetRiskMessage.

    (** Reset or release Firm, Risk Root, or Custom Group ID level lockout conditions resulting from risk profile trips or self-imposed lockouts issued via Cancel Order or Purge Orders messages *)
    Record t := {
      risk_status_id : list byte;
      risk_reset : list byte;
      clearing_firm : list byte;
      risk_root : list byte;
      target_matching_unit : N;
      custom_group_id : N;
      scratch_pad : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (risk_status_id record) = 16 /\
      Datatypes.length (risk_reset record) = 8 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (risk_root record) = 6 /\
      (target_matching_unit record < 256 ^ N.of_nat 1)%N /\
      (custom_group_id record < 256 ^ N.of_nat 2)%N /\
      (scratch_pad record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (risk_status_id record) ++
      encode_bytes 8 (risk_reset record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 6 (risk_root record) ++
      encode_uint 1 (target_matching_unit record) ++
      encode_uint 2 (custom_group_id record) ++
      encode_uint 2 (scratch_pad record).

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
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (risk_root_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (target_matching_unit_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (custom_group_id_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (scratch_pad_value, bytes) =>
                                  Some ({| risk_status_id := risk_status_id_value; risk_reset := risk_reset_value; clearing_firm := clearing_firm_value; risk_root := risk_root_value; target_matching_unit := target_matching_unit_value; custom_group_id := custom_group_id_value; scratch_pad := scratch_pad_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResetRiskMessage.

End C2OptionsBinaryOrderEntryV1010Firm.
