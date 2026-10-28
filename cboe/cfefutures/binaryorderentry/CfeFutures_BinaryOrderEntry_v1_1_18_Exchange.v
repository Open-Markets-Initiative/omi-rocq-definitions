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

Module CfeFuturesBinaryOrderEntryV1118Exchange.

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

  Module OrderAcknowledgement.

    (** Order Acknowledgement messages are sent in response to a new order message *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      order_id : N;
      side : list byte;
      price : N;
      ord_type : list byte;
      time_in_force : list byte;
      min_qty : N;
      symbol : list byte;
      capacity : list byte;
      account : list byte;
      clearing_firm : list byte;
      clearing_account : list byte;
      order_qty : N;
      prevent_match : PreventMatch.t;
      maturity_date : N;
      open_close : list byte;
      leaves_qty : N;
      base_liquidity_indicator : list byte;
      expire_time : N;
      sub_liquidity_indicator : list byte;
      stop_px : N;
      cmta_number : N;
      cti_code : list byte;
      manual_order_indicator : list byte;
      oeo_id : list byte;
      cum_qty : N;
      frequent_trader_id : list byte;
      cust_order_handling_inst : list byte;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (time_in_force record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (account record) = 16 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      PreventMatch.bounded (prevent_match record) /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_close record) = 1 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (cmta_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cti_code record) = 1 /\
      Datatypes.length (manual_order_indicator record) = 1 /\
      Datatypes.length (oeo_id record) = 18 /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (frequent_trader_id record) = 6 /\
      Datatypes.length (cust_order_handling_inst record) = 1 /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (min_qty record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 16 (account record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 4 (order_qty record) ++
      PreventMatch.encode (prevent_match record) ++
      encode_uint 4 (maturity_date record) ++
      encode_bytes 1 (open_close record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 8 (expire_time record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 4 (cmta_number record) ++
      encode_bytes 1 (cti_code record) ++
      encode_bytes 1 (manual_order_indicator record) ++
      encode_bytes 18 (oeo_id record) ++
      encode_uint 4 (cum_qty record) ++
      encode_bytes 6 (frequent_trader_id record) ++
      encode_bytes 1 (cust_order_handling_inst record) ++
      encode_uint 8 (request_received_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
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
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (clearing_firm_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (clearing_account_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (order_qty_value, bytes) =>
                                                              match PreventMatch.decode bytes with
                                                              | None => None
                                                              | Some (prevent_match_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (maturity_date_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (open_close_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (leaves_qty_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (base_liquidity_indicator_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (expire_time_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (sub_liquidity_indicator_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (stop_px_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (cmta_number_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (cti_code_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (manual_order_indicator_value, bytes) =>
                                                                                                          match decode_bytes 18 bytes with
                                                                                                          | None => None
                                                                                                          | Some (oeo_id_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (cum_qty_value, bytes) =>
                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (frequent_trader_id_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (cust_order_handling_inst_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (request_received_time_value, bytes) =>
                                                                                                                              Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; side := side_value; price := price_value; ord_type := ord_type_value; time_in_force := time_in_force_value; min_qty := min_qty_value; symbol := symbol_value; capacity := capacity_value; account := account_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; order_qty := order_qty_value; prevent_match := prevent_match_value; maturity_date := maturity_date_value; open_close := open_close_value; leaves_qty := leaves_qty_value; base_liquidity_indicator := base_liquidity_indicator_value; expire_time := expire_time_value; sub_liquidity_indicator := sub_liquidity_indicator_value; stop_px := stop_px_value; cmta_number := cmta_number_value; cti_code := cti_code_value; manual_order_indicator := manual_order_indicator_value; oeo_id := oeo_id_value; cum_qty := cum_qty_value; frequent_trader_id := frequent_trader_id_value; cust_order_handling_inst := cust_order_handling_inst_value; request_received_time := request_received_time_value |}, bytes)
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 161.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !PreventMatch.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 bound_29]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite PreventMatch.decode_encode by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply PreventMatch.eq_dec]. Defined.

  End OrderAcknowledgement.

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

  Module OrderRejected.

    (** Order Rejected messages are sent in response to a New Order which must be rejected *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      order_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (order_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (order_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_reject_reason_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; order_reject_reason := order_reject_reason_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRejected.

  Module OrderModified.

    (** Order Modified messages are sent in response to a Modify Order to indicate that the orderhas been successfully modified *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      order_id : N;
      clearing_firm : list byte;
      price : N;
      ord_type : list byte;
      order_qty : N;
      leaves_qty : N;
      base_liquidity_indicator : list byte;
      stop_px : N;
      frequent_trader_id : list byte;
      cust_order_handling_inst : list byte;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (frequent_trader_id record) = 6 /\
      Datatypes.length (cust_order_handling_inst record) = 1 /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 6 (frequent_trader_id record) ++
      encode_bytes 1 (cust_order_handling_inst record) ++
      encode_uint 8 (request_received_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (orig_cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (clearing_firm_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_qty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (leaves_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (base_liquidity_indicator_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (stop_px_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (frequent_trader_id_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (cust_order_handling_inst_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (request_received_time_value, bytes) =>
                                                              Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; order_id := order_id_value; clearing_firm := clearing_firm_value; price := price_value; ord_type := ord_type_value; order_qty := order_qty_value; leaves_qty := leaves_qty_value; base_liquidity_indicator := base_liquidity_indicator_value; stop_px := stop_px_value; frequent_trader_id := frequent_trader_id_value; cust_order_handling_inst := cust_order_handling_inst_value; request_received_time := request_received_time_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModified.

  Module ModifyRejected.

    (** Modify Rejected messages are sent in response to a Modify Order for an order which cannot be modified *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      clearing_firm : list byte;
      modify_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (modify_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (modify_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (orig_cl_ord_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (clearing_firm_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (modify_reject_reason_value, bytes) =>
                          match decode_bytes 60 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; clearing_firm := clearing_firm_value; modify_reject_reason := modify_reject_reason_value; text := text_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 113.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyRejected.

  Module OrderExecution.

    (** AnOrder Executionis sent for each fill on an order *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      exec_id : N;
      last_shares : N;
      last_px : N;
      leaves_qty : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      side : list byte;
      symbol : list byte;
      clearing_firm : list byte;
      maturity_date : N;
      fee_code : list byte;
      trade_date : N;
      clearing_size : N;
      pending_status : list byte;
      multileg_reporting_type : list byte;
      secondary_exec_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (clearing_firm record) = 4 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (fee_code record) = 2 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      (clearing_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (pending_status record) = 1 /\
      Datatypes.length (multileg_reporting_type record) = 1 /\
      (secondary_exec_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 4 (maturity_date record) ++
      encode_bytes 2 (fee_code record) ++
      encode_uint 4 (trade_date record) ++
      encode_uint 4 (clearing_size record) ++
      encode_bytes 1 (pending_status record) ++
      encode_bytes 1 (multileg_reporting_type record) ++
      encode_uint 8 (secondary_exec_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exec_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (last_shares_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_px_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leaves_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (base_liquidity_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sub_liquidity_indicator_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (symbol_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (clearing_firm_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (maturity_date_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (fee_code_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (trade_date_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (clearing_size_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (pending_status_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (multileg_reporting_type_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (secondary_exec_id_value, bytes) =>
                                                                              Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; last_shares := last_shares_value; last_px := last_px_value; leaves_qty := leaves_qty_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; side := side_value; symbol := symbol_value; clearing_firm := clearing_firm_value; maturity_date := maturity_date_value; fee_code := fee_code_value; trade_date := trade_date_value; clearing_size := clearing_size_value; pending_status := pending_status_value; multileg_reporting_type := multileg_reporting_type_value; secondary_exec_id := secondary_exec_id_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 91.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecution.

  Module OrderExecutionOption.

    (** An Order Execution is sent for each fill on an order *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      exec_id : N;
      last_shares : N;
      last_px : N;
      leaves_qty : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      side : list byte;
      symbol : list byte;
      clearing_firm : list byte;
      security_desc : list byte;
      fee_code : list byte;
      trade_date : N;
      clearing_size : N;
      pending_status : list byte;
      multileg_reporting_type : list byte;
      secondary_exec_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (security_desc record) = 16 /\
      Datatypes.length (fee_code record) = 2 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      (clearing_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (pending_status record) = 1 /\
      Datatypes.length (multileg_reporting_type record) = 1 /\
      (secondary_exec_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 16 (security_desc record) ++
      encode_bytes 2 (fee_code record) ++
      encode_uint 4 (trade_date record) ++
      encode_uint 4 (clearing_size record) ++
      encode_bytes 1 (pending_status record) ++
      encode_bytes 1 (multileg_reporting_type record) ++
      encode_uint 8 (secondary_exec_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exec_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (last_shares_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_px_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leaves_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (base_liquidity_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sub_liquidity_indicator_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (symbol_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (clearing_firm_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (security_desc_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (fee_code_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (trade_date_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (clearing_size_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (pending_status_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (multileg_reporting_type_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (secondary_exec_id_value, bytes) =>
                                                                              Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; last_shares := last_shares_value; last_px := last_px_value; leaves_qty := leaves_qty_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; side := side_value; symbol := symbol_value; clearing_firm := clearing_firm_value; security_desc := security_desc_value; fee_code := fee_code_value; trade_date := trade_date_value; clearing_size := clearing_size_value; pending_status := pending_status_value; multileg_reporting_type := multileg_reporting_type_value; secondary_exec_id := secondary_exec_id_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 103.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutionOption.

  Module OrderCancelled.

    (** Order Cancelled message *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      cancel_reason : list byte;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (cancel_reason record) = 1 /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (cancel_reason record) ++
      encode_uint 8 (request_received_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (cancel_reason_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (request_received_time_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; cancel_reason := cancel_reason_value; request_received_time := request_received_time_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelled.

  Module CancelRejected.

    (** A Cancel Rejected message is sent in response to a Cancel Order message to indicate that the cancellation cannot occur *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      cancel_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (cancel_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (cancel_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (cancel_reject_reason_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; cancel_reject_reason := cancel_reject_reason_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelRejected.

  Module MassCancelAcknowledgement.

    (** A Mass Cancel Acknowledgment is an unsequenced message sent when a Cancel Order or Purge Orders message requesting a mass cancellation has completed cancelling all individual orders *)
    Record t := {
      transaction_time : N;
      mass_cancel_id : list byte;
      cancelled_order_count : N;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      (cancelled_order_count record < 256 ^ N.of_nat 4)%N /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_uint 4 (cancelled_order_count record) ++
      encode_uint 8 (request_received_time record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (request_received_time_value, bytes) =>
                      Some ({| transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; cancelled_order_count := cancelled_order_count_value; request_received_time := request_received_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelAcknowledgement.

  Module MassCancelRejected.

    (** A Mass Cancel Rejected message is sent in response to a Mass Cancel Order message to indicate that the mass cancellation cannot occur *)
    Record t := {
      transaction_time : N;
      mass_cancel_id : list byte;
      mass_cancel_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      Datatypes.length (mass_cancel_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_bytes 1 (mass_cancel_reject_reason record) ++
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
              | Some (mass_cancel_reject_reason_value, bytes) =>
                  match decode_bytes 60 bytes with
                  | None => None
                  | Some (text_value, bytes) =>
                      Some ({| transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; mass_cancel_reject_reason := mass_cancel_reject_reason_value; text := text_value |}, bytes)
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

  End MassCancelRejected.

  Module PurgeAcknowledgement.

    (** A Purge Acknowledgment is an unsequenced message sent when a Purge Orders message requesting an order purge has completed cancelling all individual orders *)
    Record t := {
      transaction_time : N;
      mass_cancel_id : list byte;
      cancelled_order_count : N;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      (cancelled_order_count record < 256 ^ N.of_nat 4)%N /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_uint 4 (cancelled_order_count record) ++
      encode_uint 8 (request_received_time record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (request_received_time_value, bytes) =>
                      Some ({| transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; cancelled_order_count := cancelled_order_count_value; request_received_time := request_received_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PurgeAcknowledgement.

  Module PurgeRejected.

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

  End PurgeRejected.

  Module TradeCancelCorrect.

    (** Used to provide notification that a trade has been cancelled or corrected *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      exec_ref_id : N;
      side : list byte;
      base_liquidity_indicator : list byte;
      clearing_firm : list byte;
      clearing_account : list byte;
      last_shares : N;
      last_px : N;
      corrected_price : N;
      orig_time : N;
      symbol : list byte;
      capacity : list byte;
      maturity_date : N;
      open_close : list byte;
      cmta_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (corrected_price record < 256 ^ N.of_nat 8)%N /\
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_close record) = 1 /\
      (cmta_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (corrected_price record) ++
      encode_uint 8 (orig_time record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 4 (maturity_date record) ++
      encode_bytes 1 (open_close record) ++
      encode_uint 4 (cmta_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exec_ref_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (base_liquidity_indicator_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (clearing_account_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (last_shares_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_px_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (corrected_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (orig_time_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (symbol_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (capacity_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (maturity_date_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (open_close_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (cmta_number_value, bytes) =>
                                                                      Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; exec_ref_id := exec_ref_id_value; side := side_value; base_liquidity_indicator := base_liquidity_indicator_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; last_shares := last_shares_value; last_px := last_px_value; corrected_price := corrected_price_value; orig_time := orig_time_value; symbol := symbol_value; capacity := capacity_value; maturity_date := maturity_date_value; open_close := open_close_value; cmta_number := cmta_number_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelCorrect.

  Module TradeCancelCorrectOption.

    (** Used to provide notification that an option trade has been cancelled or corrected *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      exec_ref_id : N;
      side : list byte;
      base_liquidity_indicator : list byte;
      clearing_firm : list byte;
      clearing_account : list byte;
      last_shares : N;
      last_px : N;
      corrected_price : N;
      orig_time : N;
      symbol : list byte;
      capacity : list byte;
      security_desc : list byte;
      open_close : list byte;
      cmta_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (corrected_price record < 256 ^ N.of_nat 8)%N /\
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (security_desc record) = 16 /\
      Datatypes.length (open_close record) = 1 /\
      (cmta_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (corrected_price record) ++
      encode_uint 8 (orig_time record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 16 (security_desc record) ++
      encode_bytes 1 (open_close record) ++
      encode_uint 4 (cmta_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exec_ref_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (base_liquidity_indicator_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (clearing_account_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (last_shares_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_px_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (corrected_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (orig_time_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (symbol_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (capacity_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (security_desc_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (open_close_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (cmta_number_value, bytes) =>
                                                                      Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; exec_ref_id := exec_ref_id_value; side := side_value; base_liquidity_indicator := base_liquidity_indicator_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; last_shares := last_shares_value; last_px := last_px_value; corrected_price := corrected_price_value; orig_time := orig_time_value; symbol := symbol_value; capacity := capacity_value; security_desc := security_desc_value; open_close := open_close_value; cmta_number := cmta_number_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelCorrectOption.

  Module TasRestatement.

    (** A Tas Restatement is sent post-settlement time for each TAS execution during the associated business day to communicate the updated Price and Symbol associated with the cleared execution *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      exec_id : N;
      side : list byte;
      price : N;
      symbol : list byte;
      maturity_date : N;
      last_shares : N;
      last_px : N;
      fee_code : list byte;
      trade_date : N;
      clearing_price : N;
      clearing_symbol : list byte;
      multileg_reporting_type : list byte;
      secondary_exec_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (fee_code record) = 2 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      (clearing_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_symbol record) = 8 /\
      Datatypes.length (multileg_reporting_type record) = 1 /\
      (secondary_exec_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_bytes 2 (fee_code record) ++
      encode_uint 4 (trade_date record) ++
      encode_uint 8 (clearing_price record) ++
      encode_bytes 8 (clearing_symbol record) ++
      encode_bytes 1 (multileg_reporting_type record) ++
      encode_uint 8 (secondary_exec_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (symbol_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (maturity_date_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_shares_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (last_px_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (fee_code_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (trade_date_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (clearing_price_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (clearing_symbol_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (multileg_reporting_type_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (secondary_exec_id_value, bytes) =>
                                                                      Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; exec_id := exec_id_value; side := side_value; price := price_value; symbol := symbol_value; maturity_date := maturity_date_value; last_shares := last_shares_value; last_px := last_px_value; fee_code := fee_code_value; trade_date := trade_date_value; clearing_price := clearing_price_value; clearing_symbol := clearing_symbol_value; multileg_reporting_type := multileg_reporting_type_value; secondary_exec_id := secondary_exec_id_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TasRestatement.

  Module QuoteUpdateRejected.

    (** Quote Update Rejected messages are sent in response to a Quote Update or Quote Update Option message when the entire quote block is rejected by the order handler *)
    Record t := {
      transaction_time : N;
      quote_update_id : list byte;
      quote_reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      Datatypes.length (quote_reject_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_bytes 1 (quote_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (quote_update_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_reject_reason_value, bytes) =>
                  Some ({| transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; quote_reject_reason := quote_reject_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End QuoteUpdateRejected.

  Module QuoteRestated.

    (** Quote Restatedmessages are sent to inform the TPH that an order has been asynchronously modified for some reason by CFE *)
    Record t := {
      transaction_time : N;
      quote_update_id : list byte;
      order_id : N;
      leaves_qty : N;
      working_price : N;
      quote_symbol : list byte;
      side : list byte;
      restatement_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_symbol record) = 6 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (restatement_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 6 (quote_symbol record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (restatement_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (quote_update_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (leaves_qty_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (working_price_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (quote_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (restatement_reason_value, bytes) =>
                                      Some ({| transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; working_price := working_price_value; quote_symbol := quote_symbol_value; side := side_value; restatement_reason := restatement_reason_value |}, bytes)
                                  end
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRestated.

  Module QuoteExecution.

    (** A Quote Execution message is used to indicate an execution has occurred on a resting quote *)
    Record t := {
      transaction_time : N;
      quote_update_id : list byte;
      order_id : N;
      exec_id : N;
      quote_symbol : list byte;
      clearing_firm : list byte;
      last_shares : N;
      last_px : N;
      leaves_qty : N;
      side : list byte;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      fee_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_symbol record) = 6 /\
      Datatypes.length (clearing_firm record) = 4 /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (fee_code record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 6 (quote_symbol record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 2 (fee_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (quote_update_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (quote_symbol_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (last_shares_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (leaves_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (side_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (base_liquidity_indicator_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (sub_liquidity_indicator_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (fee_code_value, bytes) =>
                                                          Some ({| transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; order_id := order_id_value; exec_id := exec_id_value; quote_symbol := quote_symbol_value; clearing_firm := clearing_firm_value; last_shares := last_shares_value; last_px := last_px_value; leaves_qty := leaves_qty_value; side := side_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; fee_code := fee_code_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteExecution.

  Module QuoteCancelled.

    (** A Quote Cancelled message will be sent to indicate an unsolicited cancellation of a quote entered with a Quote Update message *)
    Record t := {
      transaction_time : N;
      quote_update_id : list byte;
      order_id : N;
      quote_symbol : list byte;
      side : list byte;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_symbol record) = 6 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 6 (quote_symbol record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (quote_update_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (quote_symbol_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cancel_reason_value, bytes) =>
                              Some ({| transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; order_id := order_id_value; quote_symbol := quote_symbol_value; side := side_value; cancel_reason := cancel_reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteCancelled.

  Module TasQuoteRestatement.

    (** A TAS Quote Restatement is sent post-settlement time for each TAS quote execution during the associated business day to communicate the updated Price and Symbol associated with the cleared execution *)
    Record t := {
      transaction_time : N;
      quote_update_id : list byte;
      exec_id : N;
      quote_symbol : list byte;
      clearing_symbol : list byte;
      clearing_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_symbol record) = 6 /\
      Datatypes.length (clearing_symbol record) = 8 /\
      (clearing_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 6 (quote_symbol record) ++
      encode_bytes 8 (clearing_symbol record) ++
      encode_uint 8 (clearing_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (quote_update_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exec_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (quote_symbol_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (clearing_symbol_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (clearing_price_value, bytes) =>
                              Some ({| transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; exec_id := exec_id_value; quote_symbol := quote_symbol_value; clearing_symbol := clearing_symbol_value; clearing_price := clearing_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TasQuoteRestatement.

  Module ResetRiskAcknowledgement.

    (** Response to a Reset Risk request *)
    Record t := {
      risk_status_id : list byte;
      risk_reset_result : list byte;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (risk_status_id record) = 16 /\
      Datatypes.length (risk_reset_result record) = 1 /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (risk_status_id record) ++
      encode_bytes 1 (risk_reset_result record) ++
      encode_uint 8 (request_received_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (risk_status_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (risk_reset_result_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_received_time_value, bytes) =>
                  Some ({| risk_status_id := risk_status_id_value; risk_reset_result := risk_reset_result_value; request_received_time := request_received_time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResetRiskAcknowledgement.

  Module NewComplexInstrumentRejectedOption.

    (** The New Complex Instrument Rejected indicates that a requested complex strategy has been rejected *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      complex_instrument_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (complex_instrument_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (complex_instrument_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (complex_instrument_reject_reason_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; complex_instrument_reject_reason := complex_instrument_reject_reason_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewComplexInstrumentRejectedOption.

End CfeFuturesBinaryOrderEntryV1118Exchange.
