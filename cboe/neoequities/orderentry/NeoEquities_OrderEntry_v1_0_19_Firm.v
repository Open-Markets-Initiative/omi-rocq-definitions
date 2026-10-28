From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Order Entry

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

Module NeoEquitiesOrderEntryV1019Firm.

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

  Module NewOrderCaEquitiesV1.

    (** New order message for Cboe Canada Equities *)
    Record t := {
      account : list byte;
      cl_ord_id : list byte;
      broker_id : N;
      exec_inst : list byte;
      handling_inst : list byte;
      order_qty : N;
      ord_type : list byte;
      price : N;
      stop_px : N;
      side : list byte;
      symbol : list byte;
      time_in_force : list byte;
      settlement_type : N;
      fut_settl_date : N;
      ex_destination : list byte;
      max_floor : N;
      expire_time : N;
      expire_date : N;
      lei_order_origin : N;
      lei_routing_arrangement_indicator : list byte;
      umir_account_type : list byte;
      umir_user_id : list byte;
      basket_trade : N;
      program_trade : list byte;
      jitney : N;
      anonymous : list byte;
      umir_regulation_id : list byte;
      non_resident : list byte;
      bypass : list byte;
      ncib : list byte;
      no_trade_feat : list byte;
      no_trade_key : list byte;
      short_marking_exempt : list byte;
      lei_customer_account : list byte;
      lei_algorithm_id : list byte;
      customer_lei : list byte;
      broker_lei : list byte;
      routing_inst : list byte;
      display_indicator : list byte;
      matching_state_participation : list byte;
      true_min_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (account record) = 16 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      Datatypes.length (handling_inst record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (time_in_force record) = 1 /\
      (settlement_type record < 256 ^ N.of_nat 1)%N /\
      (fut_settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ex_destination record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      (expire_date record < 256 ^ N.of_nat 4)%N /\
      (lei_order_origin record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (lei_routing_arrangement_indicator record) = 1 /\
      Datatypes.length (umir_account_type record) = 1 /\
      Datatypes.length (umir_user_id record) = 12 /\
      (basket_trade record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (program_trade record) = 1 /\
      (jitney record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (anonymous record) = 1 /\
      Datatypes.length (umir_regulation_id record) = 1 /\
      Datatypes.length (non_resident record) = 1 /\
      Datatypes.length (bypass record) = 1 /\
      Datatypes.length (ncib record) = 1 /\
      Datatypes.length (no_trade_feat record) = 1 /\
      Datatypes.length (no_trade_key record) = 6 /\
      Datatypes.length (short_marking_exempt record) = 1 /\
      Datatypes.length (lei_customer_account record) = 20 /\
      Datatypes.length (lei_algorithm_id record) = 20 /\
      Datatypes.length (customer_lei record) = 52 /\
      Datatypes.length (broker_lei record) = 20 /\
      Datatypes.length (routing_inst record) = 1 /\
      Datatypes.length (display_indicator record) = 1 /\
      Datatypes.length (matching_state_participation record) = 1 /\
      (true_min_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (account record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_bytes 1 (handling_inst record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 14 (symbol record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 1 (settlement_type record) ++
      encode_uint 4 (fut_settl_date record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (expire_time record) ++
      encode_uint 4 (expire_date record) ++
      encode_uint 1 (lei_order_origin record) ++
      encode_bytes 1 (lei_routing_arrangement_indicator record) ++
      encode_bytes 1 (umir_account_type record) ++
      encode_bytes 12 (umir_user_id record) ++
      encode_uint 4 (basket_trade record) ++
      encode_bytes 1 (program_trade record) ++
      encode_uint 2 (jitney record) ++
      encode_bytes 1 (anonymous record) ++
      encode_bytes 1 (umir_regulation_id record) ++
      encode_bytes 1 (non_resident record) ++
      encode_bytes 1 (bypass record) ++
      encode_bytes 1 (ncib record) ++
      encode_bytes 1 (no_trade_feat record) ++
      encode_bytes 6 (no_trade_key record) ++
      encode_bytes 1 (short_marking_exempt record) ++
      encode_bytes 20 (lei_customer_account record) ++
      encode_bytes 20 (lei_algorithm_id record) ++
      encode_bytes 52 (customer_lei record) ++
      encode_bytes 20 (broker_lei record) ++
      encode_bytes 1 (routing_inst record) ++
      encode_bytes 1 (display_indicator record) ++
      encode_bytes 1 (matching_state_participation record) ++
      encode_uint 4 (true_min_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (account_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (exec_inst_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (handling_inst_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (stop_px_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (side_value, bytes) =>
                                              match decode_bytes 14 bytes with
                                              | None => None
                                              | Some (symbol_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (time_in_force_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (settlement_type_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (fut_settl_date_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (ex_destination_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (max_floor_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (expire_time_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (expire_date_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (lei_order_origin_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (lei_routing_arrangement_indicator_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (umir_account_type_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (umir_user_id_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (basket_trade_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (program_trade_value, bytes) =>
                                                                                                      match decode_uint 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (jitney_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (anonymous_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (umir_regulation_id_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (non_resident_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bypass_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ncib_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (no_trade_feat_value, bytes) =>
                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (no_trade_key_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (short_marking_exempt_value, bytes) =>
                                                                                                                                          match decode_bytes 20 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (lei_customer_account_value, bytes) =>
                                                                                                                                              match decode_bytes 20 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (lei_algorithm_id_value, bytes) =>
                                                                                                                                                  match decode_bytes 52 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (customer_lei_value, bytes) =>
                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (broker_lei_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (routing_inst_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (display_indicator_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (matching_state_participation_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (true_min_qty_value, bytes) =>
                                                                                                                                                                          Some ({| account := account_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; exec_inst := exec_inst_value; handling_inst := handling_inst_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; stop_px := stop_px_value; side := side_value; symbol := symbol_value; time_in_force := time_in_force_value; settlement_type := settlement_type_value; fut_settl_date := fut_settl_date_value; ex_destination := ex_destination_value; max_floor := max_floor_value; expire_time := expire_time_value; expire_date := expire_date_value; lei_order_origin := lei_order_origin_value; lei_routing_arrangement_indicator := lei_routing_arrangement_indicator_value; umir_account_type := umir_account_type_value; umir_user_id := umir_user_id_value; basket_trade := basket_trade_value; program_trade := program_trade_value; jitney := jitney_value; anonymous := anonymous_value; umir_regulation_id := umir_regulation_id_value; non_resident := non_resident_value; bypass := bypass_value; ncib := ncib_value; no_trade_feat := no_trade_feat_value; no_trade_key := no_trade_key_value; short_marking_exempt := short_marking_exempt_value; lei_customer_account := lei_customer_account_value; lei_algorithm_id := lei_algorithm_id_value; customer_lei := customer_lei_value; broker_lei := broker_lei_value; routing_inst := routing_inst_value; display_indicator := display_indicator_value; matching_state_participation := matching_state_participation_value; true_min_qty := true_min_qty_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 253.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 bound_40]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderCaEquitiesV1.

  Module NewOrderCaEquitiesV2.

    (** New order V2 message for Cboe Canada Equities, adds PegDifference *)
    Record t := {
      account : list byte;
      cl_ord_id : list byte;
      broker_id : N;
      exec_inst : list byte;
      handling_inst : list byte;
      order_qty : N;
      ord_type : list byte;
      price : N;
      stop_px : N;
      side : list byte;
      symbol : list byte;
      time_in_force : list byte;
      settlement_type : N;
      fut_settl_date : N;
      ex_destination : list byte;
      max_floor : N;
      expire_time : N;
      expire_date : N;
      lei_order_origin : N;
      lei_routing_arrangement_indicator : list byte;
      umir_account_type : list byte;
      umir_user_id : list byte;
      basket_trade : N;
      program_trade : list byte;
      jitney : N;
      anonymous : list byte;
      umir_regulation_id : list byte;
      non_resident : list byte;
      bypass : list byte;
      ncib : list byte;
      no_trade_feat : list byte;
      no_trade_key : list byte;
      short_marking_exempt : list byte;
      lei_customer_account : list byte;
      lei_algorithm_id : list byte;
      customer_lei : list byte;
      broker_lei : list byte;
      routing_inst : list byte;
      display_indicator : list byte;
      matching_state_participation : list byte;
      true_min_qty : N;
      peg_difference : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (account record) = 16 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      Datatypes.length (handling_inst record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (time_in_force record) = 1 /\
      (settlement_type record < 256 ^ N.of_nat 1)%N /\
      (fut_settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ex_destination record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      (expire_date record < 256 ^ N.of_nat 4)%N /\
      (lei_order_origin record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (lei_routing_arrangement_indicator record) = 1 /\
      Datatypes.length (umir_account_type record) = 1 /\
      Datatypes.length (umir_user_id record) = 12 /\
      (basket_trade record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (program_trade record) = 1 /\
      (jitney record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (anonymous record) = 1 /\
      Datatypes.length (umir_regulation_id record) = 1 /\
      Datatypes.length (non_resident record) = 1 /\
      Datatypes.length (bypass record) = 1 /\
      Datatypes.length (ncib record) = 1 /\
      Datatypes.length (no_trade_feat record) = 1 /\
      Datatypes.length (no_trade_key record) = 6 /\
      Datatypes.length (short_marking_exempt record) = 1 /\
      Datatypes.length (lei_customer_account record) = 20 /\
      Datatypes.length (lei_algorithm_id record) = 20 /\
      Datatypes.length (customer_lei record) = 52 /\
      Datatypes.length (broker_lei record) = 20 /\
      Datatypes.length (routing_inst record) = 1 /\
      Datatypes.length (display_indicator record) = 1 /\
      Datatypes.length (matching_state_participation record) = 1 /\
      (true_min_qty record < 256 ^ N.of_nat 4)%N /\
      (peg_difference record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (account record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_bytes 1 (handling_inst record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 14 (symbol record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 1 (settlement_type record) ++
      encode_uint 4 (fut_settl_date record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (expire_time record) ++
      encode_uint 4 (expire_date record) ++
      encode_uint 1 (lei_order_origin record) ++
      encode_bytes 1 (lei_routing_arrangement_indicator record) ++
      encode_bytes 1 (umir_account_type record) ++
      encode_bytes 12 (umir_user_id record) ++
      encode_uint 4 (basket_trade record) ++
      encode_bytes 1 (program_trade record) ++
      encode_uint 2 (jitney record) ++
      encode_bytes 1 (anonymous record) ++
      encode_bytes 1 (umir_regulation_id record) ++
      encode_bytes 1 (non_resident record) ++
      encode_bytes 1 (bypass record) ++
      encode_bytes 1 (ncib record) ++
      encode_bytes 1 (no_trade_feat record) ++
      encode_bytes 6 (no_trade_key record) ++
      encode_bytes 1 (short_marking_exempt record) ++
      encode_bytes 20 (lei_customer_account record) ++
      encode_bytes 20 (lei_algorithm_id record) ++
      encode_bytes 52 (customer_lei record) ++
      encode_bytes 20 (broker_lei record) ++
      encode_bytes 1 (routing_inst record) ++
      encode_bytes 1 (display_indicator record) ++
      encode_bytes 1 (matching_state_participation record) ++
      encode_uint 4 (true_min_qty record) ++
      encode_uint 8 (peg_difference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (account_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (exec_inst_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (handling_inst_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (stop_px_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (side_value, bytes) =>
                                              match decode_bytes 14 bytes with
                                              | None => None
                                              | Some (symbol_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (time_in_force_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (settlement_type_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (fut_settl_date_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (ex_destination_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (max_floor_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (expire_time_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (expire_date_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (lei_order_origin_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (lei_routing_arrangement_indicator_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (umir_account_type_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (umir_user_id_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (basket_trade_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (program_trade_value, bytes) =>
                                                                                                      match decode_uint 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (jitney_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (anonymous_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (umir_regulation_id_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (non_resident_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bypass_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ncib_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (no_trade_feat_value, bytes) =>
                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (no_trade_key_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (short_marking_exempt_value, bytes) =>
                                                                                                                                          match decode_bytes 20 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (lei_customer_account_value, bytes) =>
                                                                                                                                              match decode_bytes 20 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (lei_algorithm_id_value, bytes) =>
                                                                                                                                                  match decode_bytes 52 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (customer_lei_value, bytes) =>
                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (broker_lei_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (routing_inst_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (display_indicator_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (matching_state_participation_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (true_min_qty_value, bytes) =>
                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (peg_difference_value, bytes) =>
                                                                                                                                                                              Some ({| account := account_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; exec_inst := exec_inst_value; handling_inst := handling_inst_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; stop_px := stop_px_value; side := side_value; symbol := symbol_value; time_in_force := time_in_force_value; settlement_type := settlement_type_value; fut_settl_date := fut_settl_date_value; ex_destination := ex_destination_value; max_floor := max_floor_value; expire_time := expire_time_value; expire_date := expire_date_value; lei_order_origin := lei_order_origin_value; lei_routing_arrangement_indicator := lei_routing_arrangement_indicator_value; umir_account_type := umir_account_type_value; umir_user_id := umir_user_id_value; basket_trade := basket_trade_value; program_trade := program_trade_value; jitney := jitney_value; anonymous := anonymous_value; umir_regulation_id := umir_regulation_id_value; non_resident := non_resident_value; bypass := bypass_value; ncib := ncib_value; no_trade_feat := no_trade_feat_value; no_trade_key := no_trade_key_value; short_marking_exempt := short_marking_exempt_value; lei_customer_account := lei_customer_account_value; lei_algorithm_id := lei_algorithm_id_value; customer_lei := customer_lei_value; broker_lei := broker_lei_value; routing_inst := routing_inst_value; display_indicator := display_indicator_value; matching_state_participation := matching_state_participation_value; true_min_qty := true_min_qty_value; peg_difference := peg_difference_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 261.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 bound_41]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderCaEquitiesV2.

  Module ModifyOrderCaEquitiesV1.

    (** Request to modify an existing order *)
    Record t := {
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      broker_id : N;
      account : list byte;
      order_qty : N;
      price : N;
      stop_px : N;
      time_in_force : list byte;
      max_floor : N;
      expire_date : N;
      lei_order_origin : N;
      lei_routing_arrangement_indicator : list byte;
      umir_account_type : list byte;
      lei_customer_account : list byte;
      lei_algorithm_id : list byte;
      customer_lei : list byte;
      broker_lei : list byte;
      cancel_orig_on_reject : list byte;
      true_min_qty : N;
      expire_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (account record) = 16 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (expire_date record < 256 ^ N.of_nat 4)%N /\
      (lei_order_origin record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (lei_routing_arrangement_indicator record) = 1 /\
      Datatypes.length (umir_account_type record) = 1 /\
      Datatypes.length (lei_customer_account record) = 20 /\
      Datatypes.length (lei_algorithm_id record) = 20 /\
      Datatypes.length (customer_lei record) = 52 /\
      Datatypes.length (broker_lei record) = 20 /\
      Datatypes.length (cancel_orig_on_reject record) = 1 /\
      (true_min_qty record < 256 ^ N.of_nat 4)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 16 (account record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 4 (expire_date record) ++
      encode_uint 1 (lei_order_origin record) ++
      encode_bytes 1 (lei_routing_arrangement_indicator record) ++
      encode_bytes 1 (umir_account_type record) ++
      encode_bytes 20 (lei_customer_account record) ++
      encode_bytes 20 (lei_algorithm_id record) ++
      encode_bytes 52 (customer_lei record) ++
      encode_bytes 20 (broker_lei record) ++
      encode_bytes 1 (cancel_orig_on_reject record) ++
      encode_uint 4 (true_min_qty record) ++
      encode_uint 8 (expire_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (orig_cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (account_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (stop_px_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (time_in_force_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (max_floor_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (expire_date_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (lei_order_origin_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (lei_routing_arrangement_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (umir_account_type_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (lei_customer_account_value, bytes) =>
                                                              match decode_bytes 20 bytes with
                                                              | None => None
                                                              | Some (lei_algorithm_id_value, bytes) =>
                                                                  match decode_bytes 52 bytes with
                                                                  | None => None
                                                                  | Some (customer_lei_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (broker_lei_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (cancel_orig_on_reject_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (true_min_qty_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (expire_time_value, bytes) =>
                                                                                      Some ({| cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; broker_id := broker_id_value; account := account_value; order_qty := order_qty_value; price := price_value; stop_px := stop_px_value; time_in_force := time_in_force_value; max_floor := max_floor_value; expire_date := expire_date_value; lei_order_origin := lei_order_origin_value; lei_routing_arrangement_indicator := lei_routing_arrangement_indicator_value; umir_account_type := umir_account_type_value; lei_customer_account := lei_customer_account_value; lei_algorithm_id := lei_algorithm_id_value; customer_lei := customer_lei_value; broker_lei := broker_lei_value; cancel_orig_on_reject := cancel_orig_on_reject_value; true_min_qty := true_min_qty_value; expire_time := expire_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 215.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderCaEquitiesV1.

  Module CancelOrderCaEquitiesV1.

    (** Request to cancel a single order *)
    Record t := {
      broker_id : N;
      orig_cl_ord_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (broker_id record) ++
      encode_bytes 20 (orig_cl_ord_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (broker_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (orig_cl_ord_id_value, bytes) =>
              Some ({| broker_id := broker_id_value; orig_cl_ord_id := orig_cl_ord_id_value |}, bytes)
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

  End CancelOrderCaEquitiesV1.

  Module NewOrderCrossCaEquitiesV1.

    (** New Order Cross message for pre-arranged two-sided trades *)
    Record t := {
      broker_id : N;
      cross_cl_ord_id : list byte;
      cross_type : list byte;
      price : N;
      order_qty : N;
      symbol : list byte;
      settlement_type : N;
      fut_settl_date : N;
      umir_user_id : list byte;
      basket_trade : N;
      program_trade : list byte;
      non_resident : list byte;
      bypass : list byte;
      ncib : list byte;
      cross_side : list byte;
      short_marking_exempt : list byte;
      buy_umir_account_type : list byte;
      buy_account : list byte;
      buy_umir_regulation_id : list byte;
      buy_jitney : N;
      buy_lei_customer_account : list byte;
      buy_lei_algorithm_id : list byte;
      buy_customer_lei : list byte;
      buy_broker_lei : list byte;
      buy_lei_order_origin : N;
      buy_lei_routing_arrangemeant_indicator : list byte;
      sell_umir_account_type : list byte;
      sell_account : list byte;
      sell_umir_regulation_id : list byte;
      sell_jitney : N;
      sell_lei_customer_account : list byte;
      sell_lei_algorithm_id : list byte;
      sell_customer_lei : list byte;
      sell_broker_lei : list byte;
      sell_lei_order_origin : N;
      sell_lei_routing_arrangement_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cross_cl_ord_id record) = 18 /\
      Datatypes.length (cross_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 14 /\
      (settlement_type record < 256 ^ N.of_nat 1)%N /\
      (fut_settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (umir_user_id record) = 12 /\
      (basket_trade record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (program_trade record) = 1 /\
      Datatypes.length (non_resident record) = 1 /\
      Datatypes.length (bypass record) = 1 /\
      Datatypes.length (ncib record) = 1 /\
      Datatypes.length (cross_side record) = 1 /\
      Datatypes.length (short_marking_exempt record) = 1 /\
      Datatypes.length (buy_umir_account_type record) = 1 /\
      Datatypes.length (buy_account record) = 16 /\
      Datatypes.length (buy_umir_regulation_id record) = 1 /\
      (buy_jitney record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (buy_lei_customer_account record) = 20 /\
      Datatypes.length (buy_lei_algorithm_id record) = 20 /\
      Datatypes.length (buy_customer_lei record) = 52 /\
      Datatypes.length (buy_broker_lei record) = 20 /\
      (buy_lei_order_origin record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_lei_routing_arrangemeant_indicator record) = 1 /\
      Datatypes.length (sell_umir_account_type record) = 1 /\
      Datatypes.length (sell_account record) = 16 /\
      Datatypes.length (sell_umir_regulation_id record) = 1 /\
      (sell_jitney record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sell_lei_customer_account record) = 20 /\
      Datatypes.length (sell_lei_algorithm_id record) = 20 /\
      Datatypes.length (sell_customer_lei record) = 52 /\
      Datatypes.length (sell_broker_lei record) = 20 /\
      (sell_lei_order_origin record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sell_lei_routing_arrangement_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (broker_id record) ++
      encode_bytes 18 (cross_cl_ord_id record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 14 (symbol record) ++
      encode_uint 1 (settlement_type record) ++
      encode_uint 4 (fut_settl_date record) ++
      encode_bytes 12 (umir_user_id record) ++
      encode_uint 4 (basket_trade record) ++
      encode_bytes 1 (program_trade record) ++
      encode_bytes 1 (non_resident record) ++
      encode_bytes 1 (bypass record) ++
      encode_bytes 1 (ncib record) ++
      encode_bytes 1 (cross_side record) ++
      encode_bytes 1 (short_marking_exempt record) ++
      encode_bytes 1 (buy_umir_account_type record) ++
      encode_bytes 16 (buy_account record) ++
      encode_bytes 1 (buy_umir_regulation_id record) ++
      encode_uint 2 (buy_jitney record) ++
      encode_bytes 20 (buy_lei_customer_account record) ++
      encode_bytes 20 (buy_lei_algorithm_id record) ++
      encode_bytes 52 (buy_customer_lei record) ++
      encode_bytes 20 (buy_broker_lei record) ++
      encode_uint 1 (buy_lei_order_origin record) ++
      encode_bytes 1 (buy_lei_routing_arrangemeant_indicator record) ++
      encode_bytes 1 (sell_umir_account_type record) ++
      encode_bytes 16 (sell_account record) ++
      encode_bytes 1 (sell_umir_regulation_id record) ++
      encode_uint 2 (sell_jitney record) ++
      encode_bytes 20 (sell_lei_customer_account record) ++
      encode_bytes 20 (sell_lei_algorithm_id record) ++
      encode_bytes 52 (sell_customer_lei record) ++
      encode_bytes 20 (sell_broker_lei record) ++
      encode_uint 1 (sell_lei_order_origin record) ++
      encode_bytes 1 (sell_lei_routing_arrangement_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (broker_id_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (cross_cl_ord_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (cross_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_bytes 14 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (settlement_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (fut_settl_date_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (umir_user_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (basket_trade_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (program_trade_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (non_resident_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (bypass_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ncib_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (cross_side_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (short_marking_exempt_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (buy_umir_account_type_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (buy_account_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (buy_umir_regulation_id_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (buy_jitney_value, bytes) =>
                                                                                      match decode_bytes 20 bytes with
                                                                                      | None => None
                                                                                      | Some (buy_lei_customer_account_value, bytes) =>
                                                                                          match decode_bytes 20 bytes with
                                                                                          | None => None
                                                                                          | Some (buy_lei_algorithm_id_value, bytes) =>
                                                                                              match decode_bytes 52 bytes with
                                                                                              | None => None
                                                                                              | Some (buy_customer_lei_value, bytes) =>
                                                                                                  match decode_bytes 20 bytes with
                                                                                                  | None => None
                                                                                                  | Some (buy_broker_lei_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (buy_lei_order_origin_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (buy_lei_routing_arrangemeant_indicator_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (sell_umir_account_type_value, bytes) =>
                                                                                                                  match decode_bytes 16 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (sell_account_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (sell_umir_regulation_id_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (sell_jitney_value, bytes) =>
                                                                                                                              match decode_bytes 20 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (sell_lei_customer_account_value, bytes) =>
                                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (sell_lei_algorithm_id_value, bytes) =>
                                                                                                                                      match decode_bytes 52 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (sell_customer_lei_value, bytes) =>
                                                                                                                                          match decode_bytes 20 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (sell_broker_lei_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (sell_lei_order_origin_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (sell_lei_routing_arrangement_indicator_value, bytes) =>
                                                                                                                                                      Some ({| broker_id := broker_id_value; cross_cl_ord_id := cross_cl_ord_id_value; cross_type := cross_type_value; price := price_value; order_qty := order_qty_value; symbol := symbol_value; settlement_type := settlement_type_value; fut_settl_date := fut_settl_date_value; umir_user_id := umir_user_id_value; basket_trade := basket_trade_value; program_trade := program_trade_value; non_resident := non_resident_value; bypass := bypass_value; ncib := ncib_value; cross_side := cross_side_value; short_marking_exempt := short_marking_exempt_value; buy_umir_account_type := buy_umir_account_type_value; buy_account := buy_account_value; buy_umir_regulation_id := buy_umir_regulation_id_value; buy_jitney := buy_jitney_value; buy_lei_customer_account := buy_lei_customer_account_value; buy_lei_algorithm_id := buy_lei_algorithm_id_value; buy_customer_lei := buy_customer_lei_value; buy_broker_lei := buy_broker_lei_value; buy_lei_order_origin := buy_lei_order_origin_value; buy_lei_routing_arrangemeant_indicator := buy_lei_routing_arrangemeant_indicator_value; sell_umir_account_type := sell_umir_account_type_value; sell_account := sell_account_value; sell_umir_regulation_id := sell_umir_regulation_id_value; sell_jitney := sell_jitney_value; sell_lei_customer_account := sell_lei_customer_account_value; sell_lei_algorithm_id := sell_lei_algorithm_id_value; sell_customer_lei := sell_customer_lei_value; sell_broker_lei := sell_broker_lei_value; sell_lei_order_origin := sell_lei_order_origin_value; sell_lei_routing_arrangement_indicator := sell_lei_routing_arrangement_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 342.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 bound_35]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderCrossCaEquitiesV1.

  Module NewOrderCrossCaEquitiesV2.

    (** New Order Cross V2 message with Anonymous flag *)
    Record t := {
      broker_id : N;
      cross_cl_ord_id : list byte;
      cross_type : list byte;
      price : N;
      order_qty : N;
      symbol : list byte;
      settlement_type : N;
      fut_settl_date : N;
      umir_user_id : list byte;
      basket_trade : N;
      program_trade : list byte;
      non_resident : list byte;
      bypass : list byte;
      ncib : list byte;
      cross_side : list byte;
      short_marking_exempt : list byte;
      buy_umir_account_type : list byte;
      buy_account : list byte;
      buy_umir_regulation_id : list byte;
      buy_jitney : N;
      buy_lei_customer_account : list byte;
      buy_lei_algorithm_id : list byte;
      buy_customer_lei : list byte;
      buy_broker_lei : list byte;
      buy_lei_order_origin : N;
      buy_lei_routing_arrangement_indicator : list byte;
      sell_umir_account_type : list byte;
      sell_account : list byte;
      sell_umir_regulation_id : list byte;
      sell_jitney : N;
      sell_lei_customer_account : list byte;
      sell_lei_algorithm_id : list byte;
      sell_customer_lei : list byte;
      sell_broker_lei : list byte;
      sell_lei_order_origin : N;
      sell_lei_routing_arrangement_indicator : list byte;
      anonymous : list byte;
      reserved : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cross_cl_ord_id record) = 18 /\
      Datatypes.length (cross_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 14 /\
      (settlement_type record < 256 ^ N.of_nat 1)%N /\
      (fut_settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (umir_user_id record) = 12 /\
      (basket_trade record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (program_trade record) = 1 /\
      Datatypes.length (non_resident record) = 1 /\
      Datatypes.length (bypass record) = 1 /\
      Datatypes.length (ncib record) = 1 /\
      Datatypes.length (cross_side record) = 1 /\
      Datatypes.length (short_marking_exempt record) = 1 /\
      Datatypes.length (buy_umir_account_type record) = 1 /\
      Datatypes.length (buy_account record) = 16 /\
      Datatypes.length (buy_umir_regulation_id record) = 1 /\
      (buy_jitney record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (buy_lei_customer_account record) = 20 /\
      Datatypes.length (buy_lei_algorithm_id record) = 20 /\
      Datatypes.length (buy_customer_lei record) = 52 /\
      Datatypes.length (buy_broker_lei record) = 20 /\
      (buy_lei_order_origin record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_lei_routing_arrangement_indicator record) = 1 /\
      Datatypes.length (sell_umir_account_type record) = 1 /\
      Datatypes.length (sell_account record) = 16 /\
      Datatypes.length (sell_umir_regulation_id record) = 1 /\
      (sell_jitney record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sell_lei_customer_account record) = 20 /\
      Datatypes.length (sell_lei_algorithm_id record) = 20 /\
      Datatypes.length (sell_customer_lei record) = 52 /\
      Datatypes.length (sell_broker_lei record) = 20 /\
      (sell_lei_order_origin record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sell_lei_routing_arrangement_indicator record) = 1 /\
      Datatypes.length (anonymous record) = 1 /\
      (reserved record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (broker_id record) ++
      encode_bytes 18 (cross_cl_ord_id record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 14 (symbol record) ++
      encode_uint 1 (settlement_type record) ++
      encode_uint 4 (fut_settl_date record) ++
      encode_bytes 12 (umir_user_id record) ++
      encode_uint 4 (basket_trade record) ++
      encode_bytes 1 (program_trade record) ++
      encode_bytes 1 (non_resident record) ++
      encode_bytes 1 (bypass record) ++
      encode_bytes 1 (ncib record) ++
      encode_bytes 1 (cross_side record) ++
      encode_bytes 1 (short_marking_exempt record) ++
      encode_bytes 1 (buy_umir_account_type record) ++
      encode_bytes 16 (buy_account record) ++
      encode_bytes 1 (buy_umir_regulation_id record) ++
      encode_uint 2 (buy_jitney record) ++
      encode_bytes 20 (buy_lei_customer_account record) ++
      encode_bytes 20 (buy_lei_algorithm_id record) ++
      encode_bytes 52 (buy_customer_lei record) ++
      encode_bytes 20 (buy_broker_lei record) ++
      encode_uint 1 (buy_lei_order_origin record) ++
      encode_bytes 1 (buy_lei_routing_arrangement_indicator record) ++
      encode_bytes 1 (sell_umir_account_type record) ++
      encode_bytes 16 (sell_account record) ++
      encode_bytes 1 (sell_umir_regulation_id record) ++
      encode_uint 2 (sell_jitney record) ++
      encode_bytes 20 (sell_lei_customer_account record) ++
      encode_bytes 20 (sell_lei_algorithm_id record) ++
      encode_bytes 52 (sell_customer_lei record) ++
      encode_bytes 20 (sell_broker_lei record) ++
      encode_uint 1 (sell_lei_order_origin record) ++
      encode_bytes 1 (sell_lei_routing_arrangement_indicator record) ++
      encode_bytes 1 (anonymous record) ++
      encode_uint 4 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (broker_id_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (cross_cl_ord_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (cross_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_bytes 14 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (settlement_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (fut_settl_date_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (umir_user_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (basket_trade_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (program_trade_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (non_resident_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (bypass_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ncib_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (cross_side_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (short_marking_exempt_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (buy_umir_account_type_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (buy_account_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (buy_umir_regulation_id_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (buy_jitney_value, bytes) =>
                                                                                      match decode_bytes 20 bytes with
                                                                                      | None => None
                                                                                      | Some (buy_lei_customer_account_value, bytes) =>
                                                                                          match decode_bytes 20 bytes with
                                                                                          | None => None
                                                                                          | Some (buy_lei_algorithm_id_value, bytes) =>
                                                                                              match decode_bytes 52 bytes with
                                                                                              | None => None
                                                                                              | Some (buy_customer_lei_value, bytes) =>
                                                                                                  match decode_bytes 20 bytes with
                                                                                                  | None => None
                                                                                                  | Some (buy_broker_lei_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (buy_lei_order_origin_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (buy_lei_routing_arrangement_indicator_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (sell_umir_account_type_value, bytes) =>
                                                                                                                  match decode_bytes 16 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (sell_account_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (sell_umir_regulation_id_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (sell_jitney_value, bytes) =>
                                                                                                                              match decode_bytes 20 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (sell_lei_customer_account_value, bytes) =>
                                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (sell_lei_algorithm_id_value, bytes) =>
                                                                                                                                      match decode_bytes 52 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (sell_customer_lei_value, bytes) =>
                                                                                                                                          match decode_bytes 20 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (sell_broker_lei_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (sell_lei_order_origin_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (sell_lei_routing_arrangement_indicator_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (anonymous_value, bytes) =>
                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (reserved_value, bytes) =>
                                                                                                                                                              Some ({| broker_id := broker_id_value; cross_cl_ord_id := cross_cl_ord_id_value; cross_type := cross_type_value; price := price_value; order_qty := order_qty_value; symbol := symbol_value; settlement_type := settlement_type_value; fut_settl_date := fut_settl_date_value; umir_user_id := umir_user_id_value; basket_trade := basket_trade_value; program_trade := program_trade_value; non_resident := non_resident_value; bypass := bypass_value; ncib := ncib_value; cross_side := cross_side_value; short_marking_exempt := short_marking_exempt_value; buy_umir_account_type := buy_umir_account_type_value; buy_account := buy_account_value; buy_umir_regulation_id := buy_umir_regulation_id_value; buy_jitney := buy_jitney_value; buy_lei_customer_account := buy_lei_customer_account_value; buy_lei_algorithm_id := buy_lei_algorithm_id_value; buy_customer_lei := buy_customer_lei_value; buy_broker_lei := buy_broker_lei_value; buy_lei_order_origin := buy_lei_order_origin_value; buy_lei_routing_arrangement_indicator := buy_lei_routing_arrangement_indicator_value; sell_umir_account_type := sell_umir_account_type_value; sell_account := sell_account_value; sell_umir_regulation_id := sell_umir_regulation_id_value; sell_jitney := sell_jitney_value; sell_lei_customer_account := sell_lei_customer_account_value; sell_lei_algorithm_id := sell_lei_algorithm_id_value; sell_customer_lei := sell_customer_lei_value; sell_broker_lei := sell_broker_lei_value; sell_lei_order_origin := sell_lei_order_origin_value; sell_lei_routing_arrangement_indicator := sell_lei_routing_arrangement_indicator_value; anonymous := anonymous_value; reserved := reserved_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 347.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 bound_37]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderCrossCaEquitiesV2.

End NeoEquitiesOrderEntryV1019Firm.
