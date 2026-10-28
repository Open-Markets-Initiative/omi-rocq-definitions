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

Module NeoEquitiesOrderEntryV1019Exchange.

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

  Module OrderAcknowledgementCaEquitiesV1.

    (** Order Acknowledgement sent in response to a New Order message *)
    Record t := {
      transaction_time : N;
      account : list byte;
      cl_ord_id : list byte;
      broker_id : N;
      order_id : N;
      exec_inst : list byte;
      order_qty : N;
      ord_type : list byte;
      price : N;
      stop_px : N;
      working_price : N;
      side : list byte;
      short_marking_exempt : list byte;
      symbol : list byte;
      time_in_force : list byte;
      max_floor : N;
      expire_time : N;
      ex_destination : list byte;
      no_trade_feat : list byte;
      no_trade_key : list byte;
      base_liquidity_indicator : list byte;
      true_min_qty : N;
      expire_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account record) = 16 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (short_marking_exempt record) = 1 /\
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (time_in_force record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ex_destination record) = 1 /\
      Datatypes.length (no_trade_feat record) = 1 /\
      Datatypes.length (no_trade_key record) = 6 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (true_min_qty record < 256 ^ N.of_nat 4)%N /\
      (expire_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (account record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (short_marking_exempt record) ++
      encode_bytes 14 (symbol record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (expire_time record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_bytes 1 (no_trade_feat record) ++
      encode_bytes 6 (no_trade_key record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 4 (true_min_qty record) ++
      encode_uint 4 (expire_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (account_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (broker_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (exec_inst_value, bytes) =>
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
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (working_price_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (side_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (short_marking_exempt_value, bytes) =>
                                                          match decode_bytes 14 bytes with
                                                          | None => None
                                                          | Some (symbol_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (time_in_force_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (max_floor_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (expire_time_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (ex_destination_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (no_trade_feat_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (no_trade_key_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (base_liquidity_indicator_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (true_min_qty_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (expire_date_value, bytes) =>
                                                                                                  Some ({| transaction_time := transaction_time_value; account := account_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; order_id := order_id_value; exec_inst := exec_inst_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; stop_px := stop_px_value; working_price := working_price_value; side := side_value; short_marking_exempt := short_marking_exempt_value; symbol := symbol_value; time_in_force := time_in_force_value; max_floor := max_floor_value; expire_time := expire_time_value; ex_destination := ex_destination_value; no_trade_feat := no_trade_feat_value; no_trade_key := no_trade_key_value; base_liquidity_indicator := base_liquidity_indicator_value; true_min_qty := true_min_qty_value; expire_date := expire_date_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 130.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAcknowledgementCaEquitiesV1.

  Module OrderRejectedCaEquitiesV1.

    (** Order Rejected message sent in response to a New Order or New Order Cross that must be rejected *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      broker_id : N;
      order_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 1 (order_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_reject_reason_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; order_reject_reason := order_reject_reason_value; text := text_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRejectedCaEquitiesV1.

  Module OrderModifiedCaEquitiesV1.

    (** Order Modified message sent in response to a Modify Order indicating successful modification *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      broker_id : N;
      order_id : N;
      account : list byte;
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
      order_qty : N;
      orig_cl_ord_id : list byte;
      leaves_qty : N;
      price : N;
      stop_px : N;
      true_min_qty : N;
      secondary_order_id : N;
      expire_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account record) = 16 /\
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
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (true_min_qty record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (account record) ++
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
      encode_uint 4 (order_qty record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 4 (true_min_qty record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 8 (expire_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (account_value, bytes) =>
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
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (order_qty_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (orig_cl_ord_id_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (leaves_qty_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (price_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (stop_px_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (true_min_qty_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (secondary_order_id_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (expire_time_value, bytes) =>
                                                                                                  Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; order_id := order_id_value; account := account_value; time_in_force := time_in_force_value; max_floor := max_floor_value; expire_date := expire_date_value; lei_order_origin := lei_order_origin_value; lei_routing_arrangement_indicator := lei_routing_arrangement_indicator_value; umir_account_type := umir_account_type_value; lei_customer_account := lei_customer_account_value; lei_algorithm_id := lei_algorithm_id_value; customer_lei := customer_lei_value; broker_lei := broker_lei_value; order_qty := order_qty_value; orig_cl_ord_id := orig_cl_ord_id_value; leaves_qty := leaves_qty_value; price := price_value; stop_px := stop_px_value; true_min_qty := true_min_qty_value; secondary_order_id := secondary_order_id_value; expire_time := expire_time_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 242.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifiedCaEquitiesV1.

  Module ModifyRejectedCaEquitiesV1.

    (** Modify Rejected message sent in response to a Modify Order that cannot be modified *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      broker_id : N;
      orig_cl_ord_id : list byte;
      text : list byte;
      modify_reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (text record) = 60 /\
      Datatypes.length (modify_reject_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 60 (text record) ++
      encode_bytes 1 (modify_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (modify_reject_reason_value, bytes) =>
                              Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; orig_cl_ord_id := orig_cl_ord_id_value; text := text_value; modify_reject_reason := modify_reject_reason_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyRejectedCaEquitiesV1.

  Module OrderRestatedCaEquitiesV1.

    (** Order Restated message sent when iceberg order reloads or when self-trade protection reduces an order *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      broker_id : N;
      order_id : N;
      order_qty : N;
      leaves_qty : N;
      secondary_order_id : N;
      last_px : N;
      last_shares : N;
      base_liquidity_indicator : list byte;
      price : N;
      true_min_qty : N;
      restatement_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (true_min_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (restatement_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_shares record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (true_min_qty record) ++
      encode_bytes 1 (restatement_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_qty_value, bytes) =>
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
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (true_min_qty_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (restatement_reason_value, bytes) =>
                                                          Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; order_id := order_id_value; order_qty := order_qty_value; leaves_qty := leaves_qty_value; secondary_order_id := secondary_order_id_value; last_px := last_px_value; last_shares := last_shares_value; base_liquidity_indicator := base_liquidity_indicator_value; price := price_value; true_min_qty := true_min_qty_value; restatement_reason := restatement_reason_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRestatedCaEquitiesV1.

  Module OrderExecutionCaEquitiesV1.

    (** Order Execution message sent for each fill on an order *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      exec_id : N;
      last_px : N;
      last_shares : N;
      order_id : N;
      side : list byte;
      symbol : list byte;
      trade_date : N;
      leaves_qty : N;
      contra_broker : N;
      base_liquidity_indicator : list byte;
      broker_id : N;
      principal_trade : list byte;
      wash_trade : list byte;
      no_trade_feat : list byte;
      no_trade_key : list byte;
      short_marking_exempt : list byte;
      matching_priority : N;
      is_self_trade : list byte;
      fee_code : list byte;
      ex_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 14 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (contra_broker record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (principal_trade record) = 1 /\
      Datatypes.length (wash_trade record) = 1 /\
      Datatypes.length (no_trade_feat record) = 1 /\
      Datatypes.length (no_trade_key record) = 6 /\
      Datatypes.length (short_marking_exempt record) = 1 /\
      (matching_priority record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (is_self_trade record) = 1 /\
      Datatypes.length (fee_code record) = 2 /\
      Datatypes.length (ex_destination record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 14 (symbol record) ++
      encode_uint 4 (trade_date record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 2 (contra_broker record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 1 (principal_trade record) ++
      encode_bytes 1 (wash_trade record) ++
      encode_bytes 1 (no_trade_feat record) ++
      encode_bytes 6 (no_trade_key record) ++
      encode_bytes 1 (short_marking_exempt record) ++
      encode_uint 1 (matching_priority record) ++
      encode_bytes 1 (is_self_trade record) ++
      encode_bytes 2 (fee_code record) ++
      encode_bytes 1 (ex_destination record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (last_px_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (last_shares_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_bytes 14 bytes with
                                  | None => None
                                  | Some (symbol_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (trade_date_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (contra_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (base_liquidity_indicator_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (broker_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (principal_trade_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (wash_trade_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (no_trade_feat_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (no_trade_key_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (short_marking_exempt_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (matching_priority_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (is_self_trade_value, bytes) =>
                                                                                      match decode_bytes 2 bytes with
                                                                                      | None => None
                                                                                      | Some (fee_code_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ex_destination_value, bytes) =>
                                                                                              Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; last_px := last_px_value; last_shares := last_shares_value; order_id := order_id_value; side := side_value; symbol := symbol_value; trade_date := trade_date_value; leaves_qty := leaves_qty_value; contra_broker := contra_broker_value; base_liquidity_indicator := base_liquidity_indicator_value; broker_id := broker_id_value; principal_trade := principal_trade_value; wash_trade := wash_trade_value; no_trade_feat := no_trade_feat_value; no_trade_key := no_trade_key_value; short_marking_exempt := short_marking_exempt_value; matching_priority := matching_priority_value; is_self_trade := is_self_trade_value; fee_code := fee_code_value; ex_destination := ex_destination_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 99.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutionCaEquitiesV1.

  Module OrderCancelledCaEquitiesV1.

    (** Order Cancelled message *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      broker_id : N;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (cancel_reason_value, bytes) =>
                      Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; cancel_reason := cancel_reason_value |}, bytes)
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

  End OrderCancelledCaEquitiesV1.

  Module CancelRejectedCaEquitiesV1.

    (** Cancel Rejected message sent when a Cancel Order cancellation cannot occur *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      broker_id : N;
      text : list byte;
      cancel_reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (text record) = 60 /\
      Datatypes.length (cancel_reject_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 60 (text record) ++
      encode_bytes 1 (cancel_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 60 bytes with
                  | None => None
                  | Some (text_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cancel_reject_reason_value, bytes) =>
                          Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; text := text_value; cancel_reject_reason := cancel_reject_reason_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelRejectedCaEquitiesV1.

  Module CarriedRestatementCaEquitiesV1.

    (** Carried Restatement message used to indicate restoration of a multi-day GTC or GTD order at the start of a new business day *)
    Record t := {
      transaction_time : N;
      order_id : N;
      account : list byte;
      cl_ord_id : list byte;
      broker_id : N;
      exec_inst : list byte;
      handling_inst : list byte;
      order_qty : N;
      cum_qty : N;
      leaves_qty : N;
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
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account record) = 16 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      Datatypes.length (handling_inst record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
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
      encode_uint 8 (transaction_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (account record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_bytes 1 (handling_inst record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 4 (leaves_qty record) ++
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
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
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
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (cum_qty_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
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
                                                                                                                                                                              Some ({| transaction_time := transaction_time_value; order_id := order_id_value; account := account_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; exec_inst := exec_inst_value; handling_inst := handling_inst_value; order_qty := order_qty_value; cum_qty := cum_qty_value; leaves_qty := leaves_qty_value; ord_type := ord_type_value; price := price_value; stop_px := stop_px_value; side := side_value; symbol := symbol_value; time_in_force := time_in_force_value; settlement_type := settlement_type_value; fut_settl_date := fut_settl_date_value; ex_destination := ex_destination_value; max_floor := max_floor_value; expire_date := expire_date_value; lei_order_origin := lei_order_origin_value; lei_routing_arrangement_indicator := lei_routing_arrangement_indicator_value; umir_account_type := umir_account_type_value; umir_user_id := umir_user_id_value; basket_trade := basket_trade_value; program_trade := program_trade_value; jitney := jitney_value; anonymous := anonymous_value; umir_regulation_id := umir_regulation_id_value; non_resident := non_resident_value; bypass := bypass_value; ncib := ncib_value; short_marking_exempt := short_marking_exempt_value; lei_customer_account := lei_customer_account_value; lei_algorithm_id := lei_algorithm_id_value; customer_lei := customer_lei_value; broker_lei := broker_lei_value; routing_inst := routing_inst_value; display_indicator := display_indicator_value; matching_state_participation := matching_state_participation_value; true_min_qty := true_min_qty_value |}, bytes)
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 262.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 bound_41]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
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
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CarriedRestatementCaEquitiesV1.

  Module DoneForDayCaEquitiesV1.

    (** Done For Day message representing orders persisted during the current day session to carry over to the next session *)
    Record t := {
      transaction_time : N;
      cl_ord_id : list byte;
      broker_id : N;
      symbol_8 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (broker_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol_8 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (broker_id record) ++
      encode_bytes 8 (symbol_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (broker_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (symbol_8_value, bytes) =>
                      Some ({| transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; broker_id := broker_id_value; symbol_8 := symbol_8_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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

  End DoneForDayCaEquitiesV1.

  Module TradeCancelCorrectCaEquitiesV1.

    (** Trade Cancel or Correct notification that a trade has been busted or corrected *)
    Record t := {
      transaction_time : N;
      account : list byte;
      cl_ord_id : list byte;
      exec_id : N;
      exec_ref_id : N;
      last_px : N;
      last_shares : N;
      side : list byte;
      symbol : list byte;
      base_liquidity_indicator : list byte;
      corrected_size : N;
      umir_user_id : list byte;
      corrected_price : N;
      fee_code : list byte;
      settlement_type : N;
      fut_settl_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account record) = 16 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (corrected_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (umir_user_id record) = 12 /\
      (corrected_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (fee_code record) = 2 /\
      (settlement_type record < 256 ^ N.of_nat 1)%N /\
      (fut_settl_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (account record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_shares record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 14 (symbol record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 4 (corrected_size record) ++
      encode_bytes 12 (umir_user_id record) ++
      encode_uint 8 (corrected_price record) ++
      encode_bytes 2 (fee_code record) ++
      encode_uint 1 (settlement_type record) ++
      encode_uint 4 (fut_settl_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (account_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_ref_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_px_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (last_shares_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_bytes 14 bytes with
                                      | None => None
                                      | Some (symbol_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (base_liquidity_indicator_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (corrected_size_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (umir_user_id_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (corrected_price_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (fee_code_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (settlement_type_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (fut_settl_date_value, bytes) =>
                                                                      Some ({| transaction_time := transaction_time_value; account := account_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; exec_ref_id := exec_ref_id_value; last_px := last_px_value; last_shares := last_shares_value; side := side_value; symbol := symbol_value; base_liquidity_indicator := base_liquidity_indicator_value; corrected_size := corrected_size_value; umir_user_id := umir_user_id_value; corrected_price := corrected_price_value; fee_code := fee_code_value; settlement_type := settlement_type_value; fut_settl_date := fut_settl_date_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 119.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelCorrectCaEquitiesV1.

End NeoEquitiesOrderEntryV1019Exchange.
