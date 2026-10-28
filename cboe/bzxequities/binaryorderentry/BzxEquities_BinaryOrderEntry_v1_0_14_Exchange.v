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

Module BzxEquitiesBinaryOrderEntryV1014Exchange.

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

  Module OrderAcknowledgementUsEquitiesV1.

    (** Order Acknowledgment messages are sent in response to New Order messages *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      order_id : N;
      side : list byte;
      price : N;
      ord_type : list byte;
      symbol : list byte;
      clearing_firm : list byte;
      leaves_qty : N;
      display_price : N;
      working_price : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (clearing_firm record) = 4 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
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
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (symbol_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (clearing_firm_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (display_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (working_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (base_liquidity_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (sub_liquidity_indicator_value, bytes) =>
                                                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; side := side_value; price := price_value; ord_type := ord_type_value; symbol := symbol_value; clearing_firm := clearing_firm_value; leaves_qty := leaves_qty_value; display_price := display_price_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 82.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAcknowledgementUsEquitiesV1.

  Module OrderRejectedUsEquitiesV1.

    (** Order Rejected messages are sent in response to a New Order message which must be rejected *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      order_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (order_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (order_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
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
                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; order_reject_reason := order_reject_reason_value; text := text_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 95.
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

  End OrderRejectedUsEquitiesV1.

  Module OrderModifiedUsEquitiesV1.

    (** Order Modified messages are sent in response to a Modify Request message to indicate that the order has been successfully modified *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      order_id : N;
      clearing_firm : list byte;
      symbol : list byte;
      side : list byte;
      price : N;
      ord_type : list byte;
      max_floor : N;
      order_qty : N;
      stop_px : N;
      leaves_qty : N;
      display_price : N;
      working_price : N;
      base_liquidity_indicator : list byte;
      secondary_order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 8 (secondary_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
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
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (symbol_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (max_floor_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (order_qty_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (stop_px_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (leaves_qty_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (display_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (working_price_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (base_liquidity_indicator_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (secondary_order_id_value, bytes) =>
                                                                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; order_id := order_id_value; clearing_firm := clearing_firm_value; symbol := symbol_value; side := side_value; price := price_value; ord_type := ord_type_value; max_floor := max_floor_value; order_qty := order_qty_value; stop_px := stop_px_value; leaves_qty := leaves_qty_value; display_price := display_price_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; secondary_order_id := secondary_order_id_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 125.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifiedUsEquitiesV1.

  Module OrderRestatedUsEquitiesV1.

    (** Order Restated messages are sent to inform the Member that an order has been asynchronously modified for some reason without an explicit Modify Order message request having been sent *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      order_id : N;
      clearing_firm : list byte;
      symbol : list byte;
      order_restatement_reason : list byte;
      order_qty : N;
      price : N;
      leaves_qty : N;
      display_price : N;
      working_price : N;
      base_liquidity_indicator : list byte;
      secondary_order_id : N;
      last_shares : N;
      last_px : N;
      cmc_match_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (order_restatement_reason record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (cmc_match_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (order_restatement_reason record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (cmc_match_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (clearing_firm_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (order_restatement_reason_value, bytes) =>
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
                                              | Some (display_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (working_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (base_liquidity_indicator_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (secondary_order_id_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (last_shares_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (last_px_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (cmc_match_qty_value, bytes) =>
                                                                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; clearing_firm := clearing_firm_value; symbol := symbol_value; order_restatement_reason := order_restatement_reason_value; order_qty := order_qty_value; price := price_value; leaves_qty := leaves_qty_value; display_price := display_price_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; secondary_order_id := secondary_order_id_value; last_shares := last_shares_value; last_px := last_px_value; cmc_match_qty := cmc_match_qty_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 108.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRestatedUsEquitiesV1.

  Module ModifyRejectedUsEquitiesV1.

    (** User Modify Rejected messages are sent in response to a Modify Order message for an order which cannot be modified *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      clearing_firm : list byte;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      modify_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (modify_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 1 (modify_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
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
                                  Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; clearing_firm := clearing_firm_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; modify_reject_reason := modify_reject_reason_value; text := text_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 115.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyRejectedUsEquitiesV1.

  Module OrderCancelledUsEquitiesV1.

    (** This message indicates an order has been cancelled *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      clearing_firm : list byte;
      cl_ord_id : list byte;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cancel_reason_value, bytes) =>
                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; clearing_firm := clearing_firm_value; cl_ord_id := cl_ord_id_value; cancel_reason := cancel_reason_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelledUsEquitiesV1.

  Module CancelRejectedUsEquitiesV1.

    (** A Cancel Rejected message is sent in response to a Cancel Order message to indicate that the cancellation cannot occur *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      clearing_firm : list byte;
      cl_ord_id : list byte;
      cancel_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (cancel_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (cancel_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cancel_reject_reason_value, bytes) =>
                          match decode_bytes 60 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; clearing_firm := clearing_firm_value; cl_ord_id := cl_ord_id_value; cancel_reject_reason := cancel_reject_reason_value; text := text_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 95.
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

  End CancelRejectedUsEquitiesV1.

  Module OrderExecutionUsEquitiesV1.

    (** An Order Execution message is sent for each fill on an order *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      clearing_firm : list byte;
      cl_ord_id : list byte;
      exec_id : N;
      last_shares : N;
      last_px : N;
      leaves_qty : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      contra_broker : list byte;
      side : list byte;
      symbol : list byte;
      fee_code : list byte;
      access_fee : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (contra_broker record) = 4 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (fee_code record) = 2 /\
      (access_fee record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 4 (contra_broker record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 2 (fee_code record) ++
      encode_uint 8 (access_fee record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (clearing_firm_value, bytes) =>
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
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (contra_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (side_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (symbol_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (fee_code_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (access_fee_value, bytes) =>
                                                                  Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; clearing_firm := clearing_firm_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; last_shares := last_shares_value; last_px := last_px_value; leaves_qty := leaves_qty_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; contra_broker := contra_broker_value; side := side_value; symbol := symbol_value; fee_code := fee_code_value; access_fee := access_fee_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutionUsEquitiesV1.

  Module TradeCancelCorrectUsEquitiesV1.

    (** Used to relay a trade which has been cancelled (busted) or corrected (price change only) *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      order_id : N;
      exec_ref_id : N;
      side : list byte;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      clearing_firm : list byte;
      clearing_account : list byte;
      last_shares : N;
      last_px : N;
      corrected_price : N;
      orig_time : N;
      symbol : list byte;
      capacity : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (corrected_price record < 256 ^ N.of_nat 8)%N /\
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 8 (corrected_price record) ++
      encode_uint 8 (orig_time record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_ref_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (base_liquidity_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sub_liquidity_indicator_value, bytes) =>
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
                                                                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; exec_ref_id := exec_ref_id_value; side := side_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; last_shares := last_shares_value; last_px := last_px_value; corrected_price := corrected_price_value; orig_time := orig_time_value; symbol := symbol_value; capacity := capacity_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelCorrectUsEquitiesV1.

  Module PurgeRejectedUsEquitiesV1.

    (** A Purge Rejected message is sent in response to a Purge Orders message to indicate that the mass cancellation cannot occur *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      mass_cancel_id : list byte;
      purge_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      Datatypes.length (purge_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_bytes 1 (purge_reject_reason record) ++
      encode_bytes 60 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
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
                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; purge_reject_reason := purge_reject_reason_value; text := text_value |}, bytes)
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

  End PurgeRejectedUsEquitiesV1.

  Module ResetRiskAcknowledgementUsEquitiesV1.

    (** Response to a Reset Risk message request *)
    Record t := {
      in_flight : N;
      risk_status_id : list byte;
      risk_reset_result : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (risk_status_id record) = 16 /\
      Datatypes.length (risk_reset_result record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_bytes 16 (risk_status_id record) ++
      encode_bytes 1 (risk_reset_result record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (risk_status_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (risk_reset_result_value, bytes) =>
                  Some ({| in_flight := in_flight_value; risk_status_id := risk_status_id_value; risk_reset_result := risk_reset_result_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End ResetRiskAcknowledgementUsEquitiesV1.

  Module PurgeAcknowledgementUsEquitiesV1.

    (** A Purge Acknowledgment message is an unsequenced message sent when a Purge Orders message requesting an order purge has completed canceling all individual orders *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      mass_cancel_id : list byte;
      cancelled_order_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      (cancelled_order_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_uint 4 (cancelled_order_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (mass_cancel_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cancelled_order_count_value, bytes) =>
                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; cancelled_order_count := cancelled_order_count_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PurgeAcknowledgementUsEquitiesV1.

End BzxEquitiesBinaryOrderEntryV1014Exchange.
