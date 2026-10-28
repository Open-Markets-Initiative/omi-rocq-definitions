From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Futures Binary Order Entry

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

Module CfeFuturesBinaryOrderEntryV1136Firm.

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

  Module NewOrder.

    (** New order futures message *)
    Record t := {
      cl_ord_id : list byte;
      side : list byte;
      order_qty : N;
      clearing_firm : list byte;
      clearing_account : list byte;
      price : N;
      ord_type : list byte;
      time_in_force : list byte;
      min_qty : N;
      symbol : list byte;
      capacity : list byte;
      account : list byte;
      prevent_match : PreventMatch.t;
      expire_time : N;
      maturity_date : N;
      open_close : list byte;
      cmta_number : N;
      stop_px : N;
      custom_group_id : N;
      cti_code : list byte;
      manual_order_indicator : list byte;
      oeo_id : list byte;
      frequent_trader_id : list byte;
      cust_order_handling_inst : list byte;
      country_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (side record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (time_in_force record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (account record) = 16 /\
      PreventMatch.bounded (prevent_match record) /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_close record) = 1 /\
      (cmta_number record < 256 ^ N.of_nat 4)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (custom_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cti_code record) = 1 /\
      Datatypes.length (manual_order_indicator record) = 1 /\
      Datatypes.length (oeo_id record) = 18 /\
      Datatypes.length (frequent_trader_id record) = 6 /\
      Datatypes.length (cust_order_handling_inst record) = 1 /\
      Datatypes.length (country_code record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (min_qty record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 16 (account record) ++
      PreventMatch.encode (prevent_match record) ++
      encode_uint 8 (expire_time record) ++
      encode_uint 4 (maturity_date record) ++
      encode_bytes 1 (open_close record) ++
      encode_uint 4 (cmta_number record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 2 (custom_group_id record) ++
      encode_bytes 1 (cti_code record) ++
      encode_bytes 1 (manual_order_indicator record) ++
      encode_bytes 18 (oeo_id record) ++
      encode_bytes 6 (frequent_trader_id record) ++
      encode_bytes 1 (cust_order_handling_inst record) ++
      encode_bytes 2 (country_code record).

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
                              | Some (ord_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (time_in_force_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (min_qty_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (symbol_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (capacity_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (account_value, bytes) =>
                                                      match PreventMatch.decode bytes with
                                                      | None => None
                                                      | Some (prevent_match_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (expire_time_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (maturity_date_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (open_close_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (cmta_number_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (stop_px_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (custom_group_id_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (cti_code_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (manual_order_indicator_value, bytes) =>
                                                                                          match decode_bytes 18 bytes with
                                                                                          | None => None
                                                                                          | Some (oeo_id_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (frequent_trader_id_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (cust_order_handling_inst_value, bytes) =>
                                                                                                      match decode_bytes 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (country_code_value, bytes) =>
                                                                                                          Some ({| cl_ord_id := cl_ord_id_value; side := side_value; order_qty := order_qty_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; price := price_value; ord_type := ord_type_value; time_in_force := time_in_force_value; min_qty := min_qty_value; symbol := symbol_value; capacity := capacity_value; account := account_value; prevent_match := prevent_match_value; expire_time := expire_time_value; maturity_date := maturity_date_value; open_close := open_close_value; cmta_number := cmta_number_value; stop_px := stop_px_value; custom_group_id := custom_group_id_value; cti_code := cti_code_value; manual_order_indicator := manual_order_indicator_value; oeo_id := oeo_id_value; frequent_trader_id := frequent_trader_id_value; cust_order_handling_inst := cust_order_handling_inst_value; country_code := country_code_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 131.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !PreventMatch.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite PreventMatch.decode_encode by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply PreventMatch.eq_dec]. Defined.

  End NewOrder.

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

  Module ModifyOrder.

    (** Request to modify an order *)
    Record t := {
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      clearing_firm : list byte;
      order_qty : N;
      price : N;
      ord_type : list byte;
      cancel_orig_on_reject : list byte;
      stop_px : N;
      manual_order_indicator : list byte;
      oeo_id : list byte;
      frequent_trader_id : list byte;
      cust_order_handling_inst : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (cancel_orig_on_reject record) = 1 /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (manual_order_indicator record) = 1 /\
      Datatypes.length (oeo_id record) = 18 /\
      Datatypes.length (frequent_trader_id record) = 6 /\
      Datatypes.length (cust_order_handling_inst record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (cancel_orig_on_reject record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 1 (manual_order_indicator record) ++
      encode_bytes 18 (oeo_id record) ++
      encode_bytes 6 (frequent_trader_id record) ++
      encode_bytes 1 (cust_order_handling_inst record).

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
                              | Some (cancel_orig_on_reject_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (stop_px_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (manual_order_indicator_value, bytes) =>
                                          match decode_bytes 18 bytes with
                                          | None => None
                                          | Some (oeo_id_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (frequent_trader_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (cust_order_handling_inst_value, bytes) =>
                                                      Some ({| cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; clearing_firm := clearing_firm_value; order_qty := order_qty_value; price := price_value; ord_type := ord_type_value; cancel_orig_on_reject := cancel_orig_on_reject_value; stop_px := stop_px_value; manual_order_indicator := manual_order_indicator_value; oeo_id := oeo_id_value; frequent_trader_id := frequent_trader_id_value; cust_order_handling_inst := cust_order_handling_inst_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 92.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrder.

  Module CancelOrder.

    (** Request to cancel a single order or quote *)
    Record t := {
      orig_cl_ord_id : list byte;
      clearing_firm : list byte;
      manual_order_indicator : list byte;
      oeo_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (manual_order_indicator record) = 1 /\
      Datatypes.length (oeo_id record) = 18.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (manual_order_indicator record) ++
      encode_bytes 18 (oeo_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (orig_cl_ord_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (clearing_firm_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (manual_order_indicator_value, bytes) =>
                  match decode_bytes 18 bytes with
                  | None => None
                  | Some (oeo_id_value, bytes) =>
                      Some ({| orig_cl_ord_id := orig_cl_ord_id_value; clearing_firm := clearing_firm_value; manual_order_indicator := manual_order_indicator_value; oeo_id := oeo_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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

  End CancelOrder.

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
      Datatypes.length (instruction_details record) = 11.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (clearing_firm_filter record) ++
      encode_bytes 1 (acknowledgement_style record) ++
      encode_bytes 1 (lockout_instruction record) ++
      encode_bytes 1 (instrument_type_filter record) ++
      encode_bytes 1 (gtc_order_filter record) ++
      encode_bytes 11 (instruction_details record).

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
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (instruction_details_value, bytes) =>
                              Some ({| clearing_firm_filter := clearing_firm_filter_value; acknowledgement_style := acknowledgement_style_value; lockout_instruction := lockout_instruction_value; instrument_type_filter := instrument_type_filter_value; gtc_order_filter := gtc_order_filter_value; instruction_details := instruction_details_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  Module MassCancelOrder.

    (** A Mass Cancel Order message is a request to cancel a group of orders or quotes *)
    Record t := {
      mass_cancel_id : list byte;
      clearing_firm : list byte;
      product_name : list byte;
      mass_cancel_inst : MassCancelInst.t;
      manual_order_indicator : list byte;
      oeo_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mass_cancel_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (product_name record) = 6 /\
      MassCancelInst.bounded (mass_cancel_inst record) /\
      Datatypes.length (manual_order_indicator record) = 1 /\
      Datatypes.length (oeo_id record) = 18.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (mass_cancel_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 6 (product_name record) ++
      MassCancelInst.encode (mass_cancel_inst record) ++
      encode_bytes 1 (manual_order_indicator record) ++
      encode_bytes 18 (oeo_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (mass_cancel_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (clearing_firm_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (product_name_value, bytes) =>
                  match MassCancelInst.decode bytes with
                  | None => None
                  | Some (mass_cancel_inst_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (manual_order_indicator_value, bytes) =>
                          match decode_bytes 18 bytes with
                          | None => None
                          | Some (oeo_id_value, bytes) =>
                              Some ({| mass_cancel_id := mass_cancel_id_value; clearing_firm := clearing_firm_value; product_name := product_name_value; mass_cancel_inst := mass_cancel_inst_value; manual_order_indicator := manual_order_indicator_value; oeo_id := oeo_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !MassCancelInst.encode_length. reflexivity.
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
      rewrite MassCancelInst.decode_encode by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MassCancelInst.eq_dec]. Defined.

  End MassCancelOrder.

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
      Datatypes.length (instruction_details record) = 11.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (clearing_firm_filter record) ++
      encode_bytes 1 (acknowledgement_style record) ++
      encode_bytes 1 (lockout_instruction record) ++
      encode_bytes 1 (instrument_type_filter record) ++
      encode_bytes 1 (gtc_order_filter record) ++
      encode_bytes 11 (instruction_details record).

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
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (instruction_details_value, bytes) =>
                              Some ({| clearing_firm_filter := clearing_firm_filter_value; acknowledgement_style := acknowledgement_style_value; lockout_instruction := lockout_instruction_value; instrument_type_filter := instrument_type_filter_value; gtc_order_filter := gtc_order_filter_value; instruction_details := instruction_details_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  Module PurgeOrders.

    (** Request to cancel a group of orders or quotes across all the TPH's sessions for that port’s matching unit *)
    Record t := {
      mass_cancel_id : list byte;
      clearing_firm : list byte;
      product_name : list byte;
      mass_cancel_inst : MassCancelInst2.t;
      manual_order_indicator : list byte;
      oeo_id : list byte;
      custom_group_id_cnt : N;
      custom_group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mass_cancel_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (product_name record) = 6 /\
      MassCancelInst2.bounded (mass_cancel_inst record) /\
      Datatypes.length (manual_order_indicator record) = 1 /\
      Datatypes.length (oeo_id record) = 18 /\
      (custom_group_id_cnt record < 256 ^ N.of_nat 1)%N /\
      (custom_group_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (mass_cancel_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 6 (product_name record) ++
      MassCancelInst2.encode (mass_cancel_inst record) ++
      encode_bytes 1 (manual_order_indicator record) ++
      encode_bytes 18 (oeo_id record) ++
      encode_uint 1 (custom_group_id_cnt record) ++
      encode_uint 2 (custom_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (mass_cancel_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (clearing_firm_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (product_name_value, bytes) =>
                  match MassCancelInst2.decode bytes with
                  | None => None
                  | Some (mass_cancel_inst_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (manual_order_indicator_value, bytes) =>
                          match decode_bytes 18 bytes with
                          | None => None
                          | Some (oeo_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (custom_group_id_cnt_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (custom_group_id_value, bytes) =>
                                      Some ({| mass_cancel_id := mass_cancel_id_value; clearing_firm := clearing_firm_value; product_name := product_name_value; mass_cancel_inst := mass_cancel_inst_value; manual_order_indicator := manual_order_indicator_value; oeo_id := oeo_id_value; custom_group_id_cnt := custom_group_id_cnt_value; custom_group_id := custom_group_id_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !MassCancelInst2.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite MassCancelInst2.decode_encode by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MassCancelInst2.eq_dec]. Defined.

  End PurgeOrders.

  Module ResetRisk.

    (** Reset or release Firm/EFID, Product, or Custom Group Id level lockout conditions resulting from risk profile trips or self-imposed lockouts issued viaMass Cancel Order or Purge Orders messages *)
    Record t := {
      risk_status_id : list byte;
      risk_reset : list byte;
      clearing_firm : list byte;
      product_name : list byte;
      custom_group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (risk_status_id record) = 16 /\
      Datatypes.length (risk_reset record) = 8 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (product_name record) = 6 /\
      (custom_group_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (risk_status_id record) ++
      encode_bytes 8 (risk_reset record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 6 (product_name record) ++
      encode_uint 2 (custom_group_id record).

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
                  | Some (product_name_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (custom_group_id_value, bytes) =>
                          Some ({| risk_status_id := risk_status_id_value; risk_reset := risk_reset_value; clearing_firm := clearing_firm_value; product_name := product_name_value; custom_group_id := custom_group_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResetRisk.

End CfeFuturesBinaryOrderEntryV1136Firm.
