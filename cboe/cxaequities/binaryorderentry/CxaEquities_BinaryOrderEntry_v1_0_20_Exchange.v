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

Module CxaEquitiesBinaryOrderEntryV1020Exchange.

  Module ExchangeMessageHeader.

    (** Message header of a packet sent by the exchange *)
    Record t := {
      start_of_message : N;
      message_length : N;
      exchange_message_type : N;
      matching_unit : N;
      reserved_field : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_of_message record < 256 ^ N.of_nat 2)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (exchange_message_type record < 256 ^ N.of_nat 2)%N /\
      (matching_unit record < 256 ^ N.of_nat 1)%N /\
      (reserved_field record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (start_of_message record) ++
      encode_uint 2 (message_length record) ++
      encode_uint 2 (exchange_message_type record) ++
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
              | Some (exchange_message_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (matching_unit_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_field_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (sequence_number_value, bytes) =>
                              Some ({| start_of_message := start_of_message_value; message_length := message_length_value; exchange_message_type := exchange_message_type_value; matching_unit := matching_unit_value; reserved_field := reserved_field_value; sequence_number := sequence_number_value |}, bytes)
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

  End ExchangeMessageHeader.

  Module LogoutResponseMessage.

    (** A Logout Response is usually sent in response to a Logout Request *)
    Record t := {
      logout_reason : list byte;
      logout_reason_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (logout_reason record) = 1 /\
      Datatypes.length (logout_reason_text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (logout_reason record) ++
      encode_bytes 60 (logout_reason_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (logout_reason_value, bytes) =>
          match decode_bytes 60 bytes with
          | None => None
          | Some (logout_reason_text_value, bytes) =>
              Some ({| logout_reason := logout_reason_value; logout_reason_text := logout_reason_text_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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

  End LogoutResponseMessage.

  Module OrderAcknowledgementAuEquitiesV1.

    (** Order Acknowledgement messages are sent in response to a New Order message *)
    Record t := {
      transaction_time : N;
      account : list byte;
      trading_participant_id : N;
      cl_ord_id : list byte;
      exec_inst : list byte;
      order_id : N;
      order_qty : N;
      ord_type : list byte;
      price : N;
      capacity : list byte;
      side : list byte;
      symbol : list byte;
      time_in_force : list byte;
      min_qty : N;
      max_floor : N;
      expire_time : N;
      clearing_participant_id : N;
      clearing_account : list byte;
      undisclosed : list byte;
      client_cross_ref : list byte;
      short_sell_naked_qty : N;
      short_sell_covered_qty : N;
      short_sell_long_qty : N;
      risk_group_id : N;
      no_trade_feat : list byte;
      no_trade_key : list byte;
      meqse : list byte;
      origin_of_trans : list byte;
      intermediary_id : list byte;
      directed_wholesale_indicator : list byte;
      remove_crossing_from_clearing : list byte;
      broker_preferencing : list byte;
      working_price : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      routing_inst : list byte;
      display_indicator : list byte;
      expire_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account record) = 10 /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (exec_inst record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (time_in_force record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      (clearing_participant_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_account record) = 10 /\
      Datatypes.length (undisclosed record) = 1 /\
      Datatypes.length (client_cross_ref record) = 15 /\
      (short_sell_naked_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_covered_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_long_qty record < 256 ^ N.of_nat 4)%N /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (no_trade_feat record) = 1 /\
      Datatypes.length (no_trade_key record) = 10 /\
      Datatypes.length (meqse record) = 1 /\
      Datatypes.length (origin_of_trans record) = 20 /\
      Datatypes.length (intermediary_id record) = 10 /\
      Datatypes.length (directed_wholesale_indicator record) = 1 /\
      Datatypes.length (remove_crossing_from_clearing record) = 1 /\
      Datatypes.length (broker_preferencing record) = 1 /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (routing_inst record) = 1 /\
      Datatypes.length (display_indicator record) = 1 /\
      (expire_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 10 (account record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (expire_time record) ++
      encode_uint 4 (clearing_participant_id record) ++
      encode_bytes 10 (clearing_account record) ++
      encode_bytes 1 (undisclosed record) ++
      encode_bytes 15 (client_cross_ref record) ++
      encode_uint 4 (short_sell_naked_qty record) ++
      encode_uint 4 (short_sell_covered_qty record) ++
      encode_uint 4 (short_sell_long_qty record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_bytes 1 (no_trade_feat record) ++
      encode_bytes 10 (no_trade_key record) ++
      encode_bytes 1 (meqse record) ++
      encode_bytes 20 (origin_of_trans record) ++
      encode_bytes 10 (intermediary_id record) ++
      encode_bytes 1 (directed_wholesale_indicator record) ++
      encode_bytes 1 (remove_crossing_from_clearing record) ++
      encode_bytes 1 (broker_preferencing record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 1 (routing_inst record) ++
      encode_bytes 1 (display_indicator record) ++
      encode_uint 4 (expire_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (account_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (trading_participant_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (exec_inst_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (order_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (ord_type_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (capacity_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (symbol_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (time_in_force_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (min_qty_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (max_floor_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (expire_time_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (clearing_participant_id_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (clearing_account_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (undisclosed_value, bytes) =>
                                                                                  match decode_bytes 15 bytes with
                                                                                  | None => None
                                                                                  | Some (client_cross_ref_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (short_sell_naked_qty_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (short_sell_covered_qty_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (short_sell_long_qty_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (risk_group_id_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (no_trade_feat_value, bytes) =>
                                                                                                          match decode_bytes 10 bytes with
                                                                                                          | None => None
                                                                                                          | Some (no_trade_key_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (meqse_value, bytes) =>
                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (origin_of_trans_value, bytes) =>
                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (intermediary_id_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (directed_wholesale_indicator_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (remove_crossing_from_clearing_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (broker_preferencing_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (working_price_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (base_liquidity_indicator_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (sub_liquidity_indicator_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (routing_inst_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (display_indicator_value, bytes) =>
                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (expire_date_value, bytes) =>
                                                                                                                                                              Some ({| transaction_time := transaction_time_value; account := account_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; exec_inst := exec_inst_value; order_id := order_id_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; capacity := capacity_value; side := side_value; symbol := symbol_value; time_in_force := time_in_force_value; min_qty := min_qty_value; max_floor := max_floor_value; expire_time := expire_time_value; clearing_participant_id := clearing_participant_id_value; clearing_account := clearing_account_value; undisclosed := undisclosed_value; client_cross_ref := client_cross_ref_value; short_sell_naked_qty := short_sell_naked_qty_value; short_sell_covered_qty := short_sell_covered_qty_value; short_sell_long_qty := short_sell_long_qty_value; risk_group_id := risk_group_id_value; no_trade_feat := no_trade_feat_value; no_trade_key := no_trade_key_value; meqse := meqse_value; origin_of_trans := origin_of_trans_value; intermediary_id := intermediary_id_value; directed_wholesale_indicator := directed_wholesale_indicator_value; remove_crossing_from_clearing := remove_crossing_from_clearing_value; broker_preferencing := broker_preferencing_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; routing_inst := routing_inst_value; display_indicator := display_indicator_value; expire_date := expire_date_value |}, bytes)
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 192.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAcknowledgementAuEquitiesV1.

  Module OrderRejectedAuEquitiesV1.

    (** Order Rejected messages are sent in response to a New Order which must be rejected *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      order_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (order_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (order_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_reject_reason_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; order_reject_reason := order_reject_reason_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 91.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRejectedAuEquitiesV1.

  Module OrderModifiedAuEquitiesV1.

    (** Order Modified messages are sent in response to a Modify Order to indicate that the order has been successfully modified *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      exec_inst : list byte;
      order_qty : N;
      orig_cl_ord_id : list byte;
      price : N;
      min_qty : N;
      max_floor : N;
      leaves_qty : N;
      secondary_order_id : N;
      short_sell_naked_qty : N;
      short_sell_covered_qty : N;
      short_sell_long_qty : N;
      working_price : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (exec_inst record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (short_sell_naked_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_covered_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_long_qty record < 256 ^ N.of_nat 4)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 4 (short_sell_naked_qty record) ++
      encode_uint 4 (short_sell_covered_qty record) ++
      encode_uint 4 (short_sell_long_qty record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (exec_inst_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (orig_cl_ord_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (min_qty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (max_floor_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (secondary_order_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (short_sell_naked_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (short_sell_covered_qty_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (short_sell_long_qty_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (working_price_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (base_liquidity_indicator_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (sub_liquidity_indicator_value, bytes) =>
                                                                          Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; exec_inst := exec_inst_value; order_qty := order_qty_value; orig_cl_ord_id := orig_cl_ord_id_value; price := price_value; min_qty := min_qty_value; max_floor := max_floor_value; leaves_qty := leaves_qty_value; secondary_order_id := secondary_order_id_value; short_sell_naked_qty := short_sell_naked_qty_value; short_sell_covered_qty := short_sell_covered_qty_value; short_sell_long_qty := short_sell_long_qty_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifiedAuEquitiesV1.

  Module ModifyRejectedAuEquitiesV1.

    (** Modify Rejected messages are sent in response to a Modify Order for an order which cannot be modified *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      modify_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (modify_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 1 (modify_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (modify_reject_reason_value, bytes) =>
                          match decode_bytes 60 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; modify_reject_reason := modify_reject_reason_value; text := text_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 111.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyRejectedAuEquitiesV1.

  Module OrderRestatedAuEquitiesV1.

    (** Order restatement for an iceberg reload or a Self-Trade Protection reduction or cancellation *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      order_id : N;
      order_qty : N;
      price : N;
      leaves_qty : N;
      secondary_order_id : N;
      last_px : N;
      last_shares : N;
      base_liquidity_indicator : list byte;
      restatement_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (restatement_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_shares record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (restatement_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (secondary_order_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_px_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (last_shares_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (base_liquidity_indicator_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (restatement_reason_value, bytes) =>
                                                      Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; order_qty := order_qty_value; price := price_value; leaves_qty := leaves_qty_value; secondary_order_id := secondary_order_id_value; last_px := last_px_value; last_shares := last_shares_value; base_liquidity_indicator := base_liquidity_indicator_value; restatement_reason := restatement_reason_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRestatedAuEquitiesV1.

  Module OrderExecutionAuEquitiesV1.

    (** An Order Execution is sent for each fill on an order *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      exec_id : N;
      last_capacity : list byte;
      last_mkt : list byte;
      last_px : N;
      last_shares : N;
      side : list byte;
      symbol : list byte;
      leaves_qty : N;
      secondary_order_id : N;
      clearing_participant_id : N;
      price_improvement : N;
      transact_id : list byte;
      on_market_cross_type : list byte;
      trade_report_type : list byte;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      contra_participant_id : N;
      fee_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (last_mkt record) = 4 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 6 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (clearing_participant_id record < 256 ^ N.of_nat 4)%N /\
      (price_improvement record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (transact_id record) = 10 /\
      Datatypes.length (on_market_cross_type record) = 1 /\
      Datatypes.length (trade_report_type record) = 1 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      (contra_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (fee_code record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 4 (last_mkt record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_shares record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 4 (clearing_participant_id record) ++
      encode_uint 8 (price_improvement record) ++
      encode_bytes 10 (transact_id record) ++
      encode_bytes 1 (on_market_cross_type record) ++
      encode_bytes 1 (trade_report_type record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_uint 2 (contra_participant_id record) ++
      encode_bytes 2 (fee_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (last_capacity_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (last_mkt_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (last_px_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (last_shares_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (symbol_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (leaves_qty_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (secondary_order_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (clearing_participant_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (price_improvement_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (transact_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (on_market_cross_type_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (trade_report_type_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (base_liquidity_indicator_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (sub_liquidity_indicator_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (contra_participant_id_value, bytes) =>
                                                                                      match decode_bytes 2 bytes with
                                                                                      | None => None
                                                                                      | Some (fee_code_value, bytes) =>
                                                                                          Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; last_capacity := last_capacity_value; last_mkt := last_mkt_value; last_px := last_px_value; last_shares := last_shares_value; side := side_value; symbol := symbol_value; leaves_qty := leaves_qty_value; secondary_order_id := secondary_order_id_value; clearing_participant_id := clearing_participant_id_value; price_improvement := price_improvement_value; transact_id := transact_id_value; on_market_cross_type := on_market_cross_type_value; trade_report_type := trade_report_type_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; contra_participant_id := contra_participant_id_value; fee_code := fee_code_value |}, bytes)
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 104.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutionAuEquitiesV1.

  Module OrderCancelledAuEquitiesV1.

    (** Order Cancelled message *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (cancel_reason_value, bytes) =>
                      Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; cancel_reason := cancel_reason_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelledAuEquitiesV1.

  Module CancelRejectedAuEquitiesV1.

    (** A Cancel Rejected message is sent in response to a Cancel Order message to indicate that the cancellation cannot occur *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      cancel_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (cancel_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (cancel_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (cancel_reject_reason_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; cancel_reject_reason := cancel_reject_reason_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 91.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelRejectedAuEquitiesV1.

  Module ExecutionRestatementAuEquitiesV1.

    (** Order Execution Restated messages will be issued for all (unbroken) fills of MOC orders after the closing price has been determined *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      exec_id : N;
      last_px : N;
      last_shares : N;
      side : list byte;
      symbol : list byte;
      transact_id : list byte;
      base_liquidity_indicator : list byte;
      contra_participant_id : N;
      fee_code : list byte;
      exec_restatement_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (transact_id record) = 10 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (contra_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (fee_code record) = 2 /\
      Datatypes.length (exec_restatement_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_shares record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 10 (transact_id record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 2 (contra_participant_id record) ++
      encode_bytes 2 (fee_code record) ++
      encode_bytes 1 (exec_restatement_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_px_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (last_shares_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (symbol_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (transact_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (base_liquidity_indicator_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (contra_participant_id_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (fee_code_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (exec_restatement_reason_value, bytes) =>
                                                          Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; last_px := last_px_value; last_shares := last_shares_value; side := side_value; symbol := symbol_value; transact_id := transact_id_value; base_liquidity_indicator := base_liquidity_indicator_value; contra_participant_id := contra_participant_id_value; fee_code := fee_code_value; exec_restatement_reason := exec_restatement_reason_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionRestatementAuEquitiesV1.

  Module PurgeAcknowledgementAuEquitiesV1.

    (** A Purge Acknowledgment is an unsequenced message sent when a Purge Orders message requesting an order purge has completed cancelling all individual orders *)
    Record t := {
      transaction_time : N;
      mass_cancel_id : list byte;
      cancelled_order_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      (cancelled_order_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_uint 4 (cancelled_order_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (mass_cancel_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cancelled_order_count_value, bytes) =>
                  Some ({| transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; cancelled_order_count := cancelled_order_count_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PurgeAcknowledgementAuEquitiesV1.

  Module PurgeRejectedAuEquitiesV1.

    (** A Purge Rejected message is sent in response to a Purge Orders message to indicate that the mass cancellation cannot occur *)
    Record t := {
      transaction_time : N;
      mass_cancel_id : list byte;
      purge_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      Datatypes.length (purge_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_bytes 1 (purge_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (mass_cancel_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (purge_reject_reason_value, bytes) =>
                  match decode_bytes 60 bytes with
                  | None => None
                  | Some (text_value, bytes) =>
                      Some ({| transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; purge_reject_reason := purge_reject_reason_value; text := text_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 89.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PurgeRejectedAuEquitiesV1.

  Module TradeCancelCorrectAuEquitiesV1.

    (** Used to provide notification that a trade has been cancelled (busted) or corrected (price change only) *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      exec_ref_id : N;
      last_px : N;
      last_shares : N;
      orig_time : N;
      side : list byte;
      symbol : list byte;
      clearing_participant_id : N;
      transact_id : list byte;
      corrected_price : N;
      base_liquidity_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 6 /\
      (clearing_participant_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transact_id record) = 10 /\
      (corrected_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (orig_time record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (clearing_participant_id record) ++
      encode_bytes 10 (transact_id record) ++
      encode_uint 8 (corrected_price record) ++
      encode_bytes 1 (base_liquidity_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_ref_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_px_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (last_shares_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (orig_time_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (symbol_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (clearing_participant_id_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (transact_id_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (corrected_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (base_liquidity_indicator_value, bytes) =>
                                                          Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; exec_ref_id := exec_ref_id_value; last_px := last_px_value; last_shares := last_shares_value; orig_time := orig_time_value; side := side_value; symbol := symbol_value; clearing_participant_id := clearing_participant_id_value; transact_id := transact_id_value; corrected_price := corrected_price_value; base_liquidity_indicator := base_liquidity_indicator_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 88.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelCorrectAuEquitiesV1.

  Module OrderModifiedAuEquitiesV2.

    (** Order Modified messages are sent in response to a Modify Order, with ExpireDate for multi-day orders *)
    Record t := {
      transaction_time : N;
      trading_participant_id : N;
      cl_ord_id : list byte;
      exec_inst : list byte;
      order_qty : N;
      orig_cl_ord_id : list byte;
      price : N;
      min_qty : N;
      max_floor : N;
      leaves_qty : N;
      secondary_order_id : N;
      short_sell_naked_qty : N;
      short_sell_covered_qty : N;
      short_sell_long_qty : N;
      working_price : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      expire_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (exec_inst record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (short_sell_naked_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_covered_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_long_qty record < 256 ^ N.of_nat 4)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      (expire_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 4 (short_sell_naked_qty record) ++
      encode_uint 4 (short_sell_covered_qty record) ++
      encode_uint 4 (short_sell_long_qty record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_uint 4 (expire_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trading_participant_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (exec_inst_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (orig_cl_ord_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (min_qty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (max_floor_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (secondary_order_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (short_sell_naked_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (short_sell_covered_qty_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (short_sell_long_qty_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (working_price_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (base_liquidity_indicator_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (sub_liquidity_indicator_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (expire_date_value, bytes) =>
                                                                              Some ({| transaction_time := transaction_time_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; exec_inst := exec_inst_value; order_qty := order_qty_value; orig_cl_ord_id := orig_cl_ord_id_value; price := price_value; min_qty := min_qty_value; max_floor := max_floor_value; leaves_qty := leaves_qty_value; secondary_order_id := secondary_order_id_value; short_sell_naked_qty := short_sell_naked_qty_value; short_sell_covered_qty := short_sell_covered_qty_value; short_sell_long_qty := short_sell_long_qty_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; expire_date := expire_date_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifiedAuEquitiesV2.

  Module CarriedRestatementAuEquitiesV1.

    (** The Carried Restatement message is used to indicate the restoration of a multi-day GTC or GTD orders at the start of a new business day *)
    Record t := {
      transaction_time : N;
      account : list byte;
      trading_participant_id : N;
      cl_ord_id : list byte;
      exec_inst : list byte;
      order_id : N;
      order_qty : N;
      ord_type : list byte;
      price : N;
      capacity : list byte;
      side : list byte;
      symbol : list byte;
      time_in_force : list byte;
      min_qty : N;
      max_floor : N;
      expire_time : N;
      clearing_participant_id : N;
      clearing_account : list byte;
      undisclosed : list byte;
      client_cross_ref : list byte;
      short_sell_naked_qty : N;
      short_sell_covered_qty : N;
      short_sell_long_qty : N;
      risk_group_id : N;
      no_trade_feat : list byte;
      no_trade_key : list byte;
      meqse : list byte;
      origin_of_trans : list byte;
      intermediary_id : list byte;
      directed_wholesale_indicator : list byte;
      remove_crossing_from_clearing : list byte;
      broker_preferencing : list byte;
      routing_inst : list byte;
      display_indicator : list byte;
      expire_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account record) = 10 /\
      (trading_participant_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (exec_inst record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (time_in_force record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      (clearing_participant_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_account record) = 10 /\
      Datatypes.length (undisclosed record) = 1 /\
      Datatypes.length (client_cross_ref record) = 15 /\
      (short_sell_naked_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_covered_qty record < 256 ^ N.of_nat 4)%N /\
      (short_sell_long_qty record < 256 ^ N.of_nat 4)%N /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (no_trade_feat record) = 1 /\
      Datatypes.length (no_trade_key record) = 10 /\
      Datatypes.length (meqse record) = 1 /\
      Datatypes.length (origin_of_trans record) = 20 /\
      Datatypes.length (intermediary_id record) = 10 /\
      Datatypes.length (directed_wholesale_indicator record) = 1 /\
      Datatypes.length (remove_crossing_from_clearing record) = 1 /\
      Datatypes.length (broker_preferencing record) = 1 /\
      Datatypes.length (routing_inst record) = 1 /\
      Datatypes.length (display_indicator record) = 1 /\
      (expire_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 10 (account record) ++
      encode_uint 2 (trading_participant_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (expire_time record) ++
      encode_uint 4 (clearing_participant_id record) ++
      encode_bytes 10 (clearing_account record) ++
      encode_bytes 1 (undisclosed record) ++
      encode_bytes 15 (client_cross_ref record) ++
      encode_uint 4 (short_sell_naked_qty record) ++
      encode_uint 4 (short_sell_covered_qty record) ++
      encode_uint 4 (short_sell_long_qty record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_bytes 1 (no_trade_feat record) ++
      encode_bytes 10 (no_trade_key record) ++
      encode_bytes 1 (meqse record) ++
      encode_bytes 20 (origin_of_trans record) ++
      encode_bytes 10 (intermediary_id record) ++
      encode_bytes 1 (directed_wholesale_indicator record) ++
      encode_bytes 1 (remove_crossing_from_clearing record) ++
      encode_bytes 1 (broker_preferencing record) ++
      encode_bytes 1 (routing_inst record) ++
      encode_bytes 1 (display_indicator record) ++
      encode_uint 4 (expire_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (account_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (trading_participant_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (exec_inst_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (order_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (ord_type_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (capacity_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (symbol_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (time_in_force_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (min_qty_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (max_floor_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (expire_time_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (clearing_participant_id_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (clearing_account_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (undisclosed_value, bytes) =>
                                                                                  match decode_bytes 15 bytes with
                                                                                  | None => None
                                                                                  | Some (client_cross_ref_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (short_sell_naked_qty_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (short_sell_covered_qty_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (short_sell_long_qty_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (risk_group_id_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (no_trade_feat_value, bytes) =>
                                                                                                          match decode_bytes 10 bytes with
                                                                                                          | None => None
                                                                                                          | Some (no_trade_key_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (meqse_value, bytes) =>
                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (origin_of_trans_value, bytes) =>
                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (intermediary_id_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (directed_wholesale_indicator_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (remove_crossing_from_clearing_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (broker_preferencing_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (routing_inst_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (display_indicator_value, bytes) =>
                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (expire_date_value, bytes) =>
                                                                                                                                                  Some ({| transaction_time := transaction_time_value; account := account_value; trading_participant_id := trading_participant_id_value; cl_ord_id := cl_ord_id_value; exec_inst := exec_inst_value; order_id := order_id_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; capacity := capacity_value; side := side_value; symbol := symbol_value; time_in_force := time_in_force_value; min_qty := min_qty_value; max_floor := max_floor_value; expire_time := expire_time_value; clearing_participant_id := clearing_participant_id_value; clearing_account := clearing_account_value; undisclosed := undisclosed_value; client_cross_ref := client_cross_ref_value; short_sell_naked_qty := short_sell_naked_qty_value; short_sell_covered_qty := short_sell_covered_qty_value; short_sell_long_qty := short_sell_long_qty_value; risk_group_id := risk_group_id_value; no_trade_feat := no_trade_feat_value; no_trade_key := no_trade_key_value; meqse := meqse_value; origin_of_trans := origin_of_trans_value; intermediary_id := intermediary_id_value; directed_wholesale_indicator := directed_wholesale_indicator_value; remove_crossing_from_clearing := remove_crossing_from_clearing_value; broker_preferencing := broker_preferencing_value; routing_inst := routing_inst_value; display_indicator := display_indicator_value; expire_date := expire_date_value |}, bytes)
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 182.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 bound_34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CarriedRestatementAuEquitiesV1.

  Module DoneForDayAuEquitiesV1.

    (** Done For Day messages represent orders persisted during the current day session to carry over to the next session *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (symbol record) = 6.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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

  End DoneForDayAuEquitiesV1.

End CxaEquitiesBinaryOrderEntryV1020Exchange.
