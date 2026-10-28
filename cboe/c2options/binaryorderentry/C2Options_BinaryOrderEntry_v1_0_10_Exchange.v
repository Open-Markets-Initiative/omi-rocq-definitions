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

Module C2OptionsBinaryOrderEntryV1010Exchange.

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

  Module OrderAcknowledgementMessage.

    (** OrderAcknowledgementMessage *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      order_id : N;
      side : list byte;
      price : N;
      symbol : list byte;
      clearing_firm : list byte;
      leaves_qty : N;
      display_price : N;
      working_price : N;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      routing_firm_id : list byte;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (clearing_firm record) = 4 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_uint 8 (request_received_time record).

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
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (routing_firm_id_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (request_received_time_value, bytes) =>
                                                                  Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; side := side_value; price := price_value; symbol := symbol_value; clearing_firm := clearing_firm_value; leaves_qty := leaves_qty_value; display_price := display_price_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; routing_firm_id := routing_firm_id_value; request_received_time := request_received_time_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAcknowledgementMessage.

  Module OrderRejectedMessage.

    (** Order Rejected messages are sent in response to a New Order message which must be rejected *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      order_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (order_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
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
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (routing_firm_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (order_reject_reason_value, bytes) =>
                              match decode_bytes 60 bytes with
                              | None => None
                              | Some (text_value, bytes) =>
                                  Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; order_reject_reason := order_reject_reason_value; text := text_value |}, bytes)
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

  End OrderRejectedMessage.

  Module QuoteUpdateRejectedMessage.

    (** Quote Update Rejected messages are sent in response to a Quote Update message when the entire quote block is rejected by the order handler *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      quote_update_id : list byte;
      quote_reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      Datatypes.length (quote_reject_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_bytes 1 (quote_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_time_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (quote_update_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quote_reject_reason_value, bytes) =>
                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; quote_reject_reason := quote_reject_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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

  End QuoteUpdateRejectedMessage.

  Module OrderModifiedMessage.

    (** Order Modified messages are sent in response to a Modify Request message to indicate that the order has been successfully modified *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      order_id : N;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      symbol : list byte;
      order_qty : N;
      price : N;
      ord_type : list byte;
      max_floor : N;
      stop_px : N;
      leaves_qty : N;
      display_price : N;
      working_price : N;
      base_liquidity_indicator : list byte;
      secondary_order_id : N;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (symbol record) = 8 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 8 (request_received_time record).

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
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (routing_firm_id_value, bytes) =>
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
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (max_floor_value, bytes) =>
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
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (request_received_time_value, bytes) =>
                                                                                  Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; order_id := order_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; symbol := symbol_value; order_qty := order_qty_value; price := price_value; ord_type := ord_type_value; max_floor := max_floor_value; stop_px := stop_px_value; leaves_qty := leaves_qty_value; display_price := display_price_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; secondary_order_id := secondary_order_id_value; request_received_time := request_received_time_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 136.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderModifiedMessage.

  Module OrderRestatedMessage.

    (** Order Restated messages are sent to inform the Member that an order has been asynchronously modified *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      order_id : N;
      clearing_firm : list byte;
      routing_firm_id : list byte;
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
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
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
      (last_px record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
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
      encode_uint 8 (last_px record).

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
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (routing_firm_id_value, bytes) =>
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
                                                                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; symbol := symbol_value; order_restatement_reason := order_restatement_reason_value; order_qty := order_qty_value; price := price_value; leaves_qty := leaves_qty_value; display_price := display_price_value; working_price := working_price_value; base_liquidity_indicator := base_liquidity_indicator_value; secondary_order_id := secondary_order_id_value; last_shares := last_shares_value; last_px := last_px_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRestatedMessage.

  Module QuoteRestatedMessage.

    (** Quote Restated messages are sent to inform the Member that an order has been asynchronously modified for some reason by the Exchange *)
    Record t := {
      in_flight : N;
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
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_symbol record) = 6 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (restatement_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 6 (quote_symbol record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (restatement_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
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
                                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; working_price := working_price_value; quote_symbol := quote_symbol_value; side := side_value; restatement_reason := restatement_reason_value |}, bytes)
                                      end
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRestatedMessage.

  Module ModifyRejectedMessage.

    (** User Modify Rejected messages are sent in response to a Modify Order message for an order which cannot be modified *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      orig_cl_ord_id : list byte;
      modify_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (modify_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
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
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (clearing_firm_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (routing_firm_id_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (orig_cl_ord_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (modify_reject_reason_value, bytes) =>
                                  match decode_bytes 60 bytes with
                                  | None => None
                                  | Some (text_value, bytes) =>
                                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; orig_cl_ord_id := orig_cl_ord_id_value; modify_reject_reason := modify_reject_reason_value; text := text_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyRejectedMessage.

  Module OrderCancelledMessage.

    (** This message indicates an order has been cancelled *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      cancel_reason : list byte;
      cancel_sub_reason : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      symbol : list byte;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (cancel_reason record) = 1 /\
      Datatypes.length (cancel_sub_reason record) = 1 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (symbol record) = 8 /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 1 (cancel_reason record) ++
      encode_bytes 1 (cancel_sub_reason record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 8 (request_received_time record).

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
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (cancel_reason_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cancel_sub_reason_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (routing_firm_id_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (symbol_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (request_received_time_value, bytes) =>
                                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; cancel_reason := cancel_reason_value; cancel_sub_reason := cancel_sub_reason_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; symbol := symbol_value; request_received_time := request_received_time_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelledMessage.

  Module QuoteCancelledMessage.

    (** A Quote Cancelled message will be sent to indicate an unsolicited cancellation of a quote entered with a Quote Update message *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      quote_update_id : list byte;
      order_id : N;
      quote_symbol : list byte;
      side : list byte;
      cancel_reason : list byte;
      cancel_sub_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_symbol record) = 6 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (cancel_reason record) = 1 /\
      Datatypes.length (cancel_sub_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 6 (quote_symbol record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (cancel_reason record) ++
      encode_bytes 1 (cancel_sub_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
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
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (cancel_sub_reason_value, bytes) =>
                                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; order_id := order_id_value; quote_symbol := quote_symbol_value; side := side_value; cancel_reason := cancel_reason_value; cancel_sub_reason := cancel_sub_reason_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteCancelledMessage.

  Module CancelRejectedMessage.

    (** A Cancel Rejected message is sent in response to a Cancel Order message to indicate that the cancellation cannot occur *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      cancel_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (cancel_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 1 (cancel_reject_reason record) ++
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
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (routing_firm_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cancel_reject_reason_value, bytes) =>
                              match decode_bytes 60 bytes with
                              | None => None
                              | Some (text_value, bytes) =>
                                  Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; cancel_reject_reason := cancel_reject_reason_value; text := text_value |}, bytes)
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

  End CancelRejectedMessage.

  Module OrderExecutionMessage.

    (** An Order Execution message is sent for each fill on an order *)
    Record t := {
      in_flight : N;
      transaction_time : N;
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
      contra_trader : list byte;
      clearing_firm : list byte;
      contra_capacity : list byte;
      fee_code : list byte;
      marketing_fee_code : list byte;
      routing_firm_id : list byte;
      cross_exclusion_indicator : list byte;
      trade_date : N;
      multileg_reporting_type : list byte;
      secondary_exec_id : N;
      price_type : list byte;
      trade_through_alert_type : list byte;
      sender_location_id : list byte;
      floor_trader_acronym : list byte;
      floor_trade_time : N;
      ex_destination : list byte;
      equity_ex_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
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
      Datatypes.length (contra_trader record) = 4 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (contra_capacity record) = 1 /\
      Datatypes.length (fee_code record) = 2 /\
      Datatypes.length (marketing_fee_code record) = 2 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (cross_exclusion_indicator record) = 1 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (multileg_reporting_type record) = 1 /\
      (secondary_exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_through_alert_type record) = 1 /\
      Datatypes.length (sender_location_id record) = 1 /\
      Datatypes.length (floor_trader_acronym record) = 3 /\
      (floor_trade_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ex_destination record) = 1 /\
      Datatypes.length (equity_ex_destination record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
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
      encode_bytes 4 (contra_trader record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 1 (contra_capacity record) ++
      encode_bytes 2 (fee_code record) ++
      encode_bytes 2 (marketing_fee_code record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 1 (cross_exclusion_indicator record) ++
      encode_uint 4 (trade_date record) ++
      encode_bytes 1 (multileg_reporting_type record) ++
      encode_uint 8 (secondary_exec_id record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_through_alert_type record) ++
      encode_bytes 1 (sender_location_id record) ++
      encode_bytes 3 (floor_trader_acronym record) ++
      encode_uint 8 (floor_trade_time record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_bytes 1 (equity_ex_destination record).

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
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (contra_trader_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (clearing_firm_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (contra_capacity_value, bytes) =>
                                                                  match decode_bytes 2 bytes with
                                                                  | None => None
                                                                  | Some (fee_code_value, bytes) =>
                                                                      match decode_bytes 2 bytes with
                                                                      | None => None
                                                                      | Some (marketing_fee_code_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (routing_firm_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (cross_exclusion_indicator_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_date_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (multileg_reporting_type_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (secondary_exec_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (price_type_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_through_alert_type_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (sender_location_id_value, bytes) =>
                                                                                                          match decode_bytes 3 bytes with
                                                                                                          | None => None
                                                                                                          | Some (floor_trader_acronym_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (floor_trade_time_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ex_destination_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (equity_ex_destination_value, bytes) =>
                                                                                                                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; last_shares := last_shares_value; last_px := last_px_value; leaves_qty := leaves_qty_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; contra_broker := contra_broker_value; side := side_value; symbol := symbol_value; contra_trader := contra_trader_value; clearing_firm := clearing_firm_value; contra_capacity := contra_capacity_value; fee_code := fee_code_value; marketing_fee_code := marketing_fee_code_value; routing_firm_id := routing_firm_id_value; cross_exclusion_indicator := cross_exclusion_indicator_value; trade_date := trade_date_value; multileg_reporting_type := multileg_reporting_type_value; secondary_exec_id := secondary_exec_id_value; price_type := price_type_value; trade_through_alert_type := trade_through_alert_type_value; sender_location_id := sender_location_id_value; floor_trader_acronym := floor_trader_acronym_value; floor_trade_time := floor_trade_time_value; ex_destination := ex_destination_value; equity_ex_destination := equity_ex_destination_value |}, bytes)
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 116.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 bound_28]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutionMessage.

  Module QuoteExecutionMessage.

    (** A Quote Execution message is used to indicate an execution has occurred on a resting quote *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      quote_update_id : list byte;
      order_id : N;
      exec_id : N;
      quote_symbol : list byte;
      clearing_firm : list byte;
      last_shares : N;
      last_px : N;
      leaves_qty : N;
      contra_trader : list byte;
      contra_capacity : list byte;
      side : list byte;
      base_liquidity_indicator : list byte;
      sub_liquidity_indicator : list byte;
      fee_code : list byte;
      marketing_fee_code : list byte;
      trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_update_id record) = 16 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (quote_symbol record) = 6 /\
      Datatypes.length (clearing_firm record) = 4 /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (contra_trader record) = 4 /\
      Datatypes.length (contra_capacity record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (base_liquidity_indicator record) = 1 /\
      Datatypes.length (sub_liquidity_indicator record) = 1 /\
      Datatypes.length (fee_code record) = 2 /\
      Datatypes.length (marketing_fee_code record) = 2 /\
      (trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 16 (quote_update_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 6 (quote_symbol record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 4 (contra_trader record) ++
      encode_bytes 1 (contra_capacity record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (base_liquidity_indicator record) ++
      encode_bytes 1 (sub_liquidity_indicator record) ++
      encode_bytes 2 (fee_code record) ++
      encode_bytes 2 (marketing_fee_code record) ++
      encode_uint 4 (trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (in_flight_value, bytes) =>
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
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (contra_trader_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (contra_capacity_value, bytes) =>
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
                                                                      match decode_bytes 2 bytes with
                                                                      | None => None
                                                                      | Some (marketing_fee_code_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (trade_date_value, bytes) =>
                                                                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; quote_update_id := quote_update_id_value; order_id := order_id_value; exec_id := exec_id_value; quote_symbol := quote_symbol_value; clearing_firm := clearing_firm_value; last_shares := last_shares_value; last_px := last_px_value; leaves_qty := leaves_qty_value; contra_trader := contra_trader_value; contra_capacity := contra_capacity_value; side := side_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; fee_code := fee_code_value; marketing_fee_code := marketing_fee_code_value; trade_date := trade_date_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteExecutionMessage.

  Module TradeCancelCorrectMessage.

    (** Used to relay a trade which has been cancelled (busted) or corrected *)
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
      corrected_size : N;
      orig_time : N;
      symbol : list byte;
      maturity_date : N;
      strike_price : N;
      put_or_call : list byte;
      capacity : list byte;
      open_close : list byte;
      marketing_fee_code : list byte;
      target_party_id : list byte;
      cmta_number : N;
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
      (corrected_size record < 256 ^ N.of_nat 4)%N /\
      (orig_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (put_or_call record) = 1 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (marketing_fee_code record) = 2 /\
      Datatypes.length (target_party_id record) = 4 /\
      (cmta_number record < 256 ^ N.of_nat 4)%N.

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
      encode_uint 4 (corrected_size record) ++
      encode_uint 8 (orig_time record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 2 (marketing_fee_code record) ++
      encode_bytes 4 (target_party_id record) ++
      encode_uint 4 (cmta_number record).

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
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (corrected_size_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (orig_time_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (symbol_value, bytes) =>
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
                                                                                  | Some (capacity_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (open_close_value, bytes) =>
                                                                                          match decode_bytes 2 bytes with
                                                                                          | None => None
                                                                                          | Some (marketing_fee_code_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (target_party_id_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (cmta_number_value, bytes) =>
                                                                                                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; exec_ref_id := exec_ref_id_value; side := side_value; base_liquidity_indicator := base_liquidity_indicator_value; sub_liquidity_indicator := sub_liquidity_indicator_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; last_shares := last_shares_value; last_px := last_px_value; corrected_price := corrected_price_value; corrected_size := corrected_size_value; orig_time := orig_time_value; symbol := symbol_value; maturity_date := maturity_date_value; strike_price := strike_price_value; put_or_call := put_or_call_value; capacity := capacity_value; open_close := open_close_value; marketing_fee_code := marketing_fee_code_value; target_party_id := target_party_id_value; cmta_number := cmta_number_value |}, bytes)
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 122.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 bound_23]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelCorrectMessage.

  Module PurgeRejectedMessage.

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

  End PurgeRejectedMessage.

  Module ResetRiskAcknowledgementMessage.

    (** Response to a Reset Risk message request *)
    Record t := {
      in_flight : N;
      risk_status_id : list byte;
      risk_reset_result : list byte;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (risk_status_id record) = 16 /\
      Datatypes.length (risk_reset_result record) = 1 /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_bytes 16 (risk_status_id record) ++
      encode_bytes 1 (risk_reset_result record) ++
      encode_uint 8 (request_received_time record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (request_received_time_value, bytes) =>
                      Some ({| in_flight := in_flight_value; risk_status_id := risk_status_id_value; risk_reset_result := risk_reset_result_value; request_received_time := request_received_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResetRiskAcknowledgementMessage.

  Module MassCancelAcknowledgmentMessage.

    (** A Mass Cancel Acknowledgment message is an unsequenced message sent when a Mass Cancel Order message requesting a mass cancellation has completed canceling all individual orders *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      mass_cancel_id : list byte;
      cancelled_order_count : N;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      (cancelled_order_count record < 256 ^ N.of_nat 4)%N /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_uint 4 (cancelled_order_count record) ++
      encode_uint 8 (request_received_time record).

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
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (request_received_time_value, bytes) =>
                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; cancelled_order_count := cancelled_order_count_value; request_received_time := request_received_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelAcknowledgmentMessage.

  Module MassCancelRejectedMessage.

    (** A Mass Cancel Rejected message is sent in response to a Mass Cancel message to indicate that the mass cancellation cannot occur *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      mass_cancel_id : list byte;
      mass_cancel_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      Datatypes.length (mass_cancel_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_bytes 1 (mass_cancel_reject_reason record) ++
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
                  | Some (mass_cancel_reject_reason_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; mass_cancel_reject_reason := mass_cancel_reject_reason_value; text := text_value |}, bytes)
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

  End MassCancelRejectedMessage.

  Module PurgeAcknowledgementMessage.

    (** A Purge Acknowledgment message is an unsequenced message sent when a Purge Orders message requesting an order purge has completed canceling all individual orders *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      mass_cancel_id : list byte;
      cancelled_order_count : N;
      source_matching_unit : N;
      request_received_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      (cancelled_order_count record < 256 ^ N.of_nat 4)%N /\
      (source_matching_unit record < 256 ^ N.of_nat 1)%N /\
      (request_received_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_uint 4 (cancelled_order_count record) ++
      encode_uint 1 (source_matching_unit record) ++
      encode_uint 8 (request_received_time record).

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
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (source_matching_unit_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (request_received_time_value, bytes) =>
                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; cancelled_order_count := cancelled_order_count_value; source_matching_unit := source_matching_unit_value; request_received_time := request_received_time_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PurgeAcknowledgementMessage.

  Module PurgeNotificationMessage.

    (** One Purge Notification message is sent for each matching unit that cancelled orders for that order entry port *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      mass_cancel_id : list byte;
      cancelled_order_count : N;
      source_matching_unit : N;
      clearing_firm : list byte;
      risk_root : list byte;
      mass_cancel_lockout : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mass_cancel_id record) = 20 /\
      (cancelled_order_count record < 256 ^ N.of_nat 4)%N /\
      (source_matching_unit record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (risk_root record) = 6 /\
      Datatypes.length (mass_cancel_lockout record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (mass_cancel_id record) ++
      encode_uint 4 (cancelled_order_count record) ++
      encode_uint 1 (source_matching_unit record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 6 (risk_root record) ++
      encode_bytes 1 (mass_cancel_lockout record).

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
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (source_matching_unit_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_firm_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (risk_root_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (mass_cancel_lockout_value, bytes) =>
                                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; mass_cancel_id := mass_cancel_id_value; cancelled_order_count := cancelled_order_count_value; source_matching_unit := source_matching_unit_value; clearing_firm := clearing_firm_value; risk_root := risk_root_value; mass_cancel_lockout := mass_cancel_lockout_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PurgeNotificationMessage.

  Module NewComplexInstrumentRejectedMessage.

    (** The New Complex Instrument Rejected message is used to indicate that a requested complex strategy has been rejected *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      no_of_securities : N;
      order_reject_reason : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (no_of_securities record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_reject_reason record) = 1 /\
      Datatypes.length (text record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 4 (no_of_securities record) ++
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
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (no_of_securities_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_reject_reason_value, bytes) =>
                          match decode_bytes 60 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; no_of_securities := no_of_securities_value; order_reject_reason := order_reject_reason_value; text := text_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewComplexInstrumentRejectedMessage.

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

  Module CarriedRestatementMessage.

    (** The Carried Restatement message is used to indicate the restoration of a multi-day GTC or GTD order at the start of a new business day *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      order_id : N;
      side : list byte;
      price : N;
      exec_inst : list byte;
      ord_type : list byte;
      time_in_force : list byte;
      min_qty : N;
      symbol : list byte;
      capacity : list byte;
      account : list byte;
      clearing_firm : list byte;
      clearing_account : list byte;
      display_indicator : list byte;
      max_floor : N;
      order_qty : N;
      prevent_match : PreventMatch.t;
      maturity_date : N;
      strike_price : N;
      put_or_call : list byte;
      open_close : list byte;
      leaves_qty : N;
      display_price : N;
      working_price : N;
      expire_time : N;
      attributed_quote : list byte;
      stop_px : N;
      routing_inst : list byte;
      rout_strategy : list byte;
      route_delivery_method : list byte;
      ex_destination : list byte;
      target_party_id : list byte;
      auction_id : N;
      cmta_number : N;
      routing_firm_id : list byte;
      clearing_optional_data : list byte;
      cum_qty : N;
      drill_thru_protection : N;
      equity_party_id : list byte;
      client_id_attr : list byte;
      frequent_trader_id : list byte;
      session_eligibility : list byte;
      combo_order : list byte;
      compression : list byte;
      floor_destination : list byte;
      floor_routing_inst : list byte;
      order_origin : list byte;
      price_type : list byte;
      strategy_id : list byte;
      held : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      Datatypes.length (ord_type record) = 1 /\
      Datatypes.length (time_in_force record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (account record) = 16 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (clearing_account record) = 4 /\
      Datatypes.length (display_indicator record) = 1 /\
      (max_floor record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      PreventMatch.bounded (prevent_match record) /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (put_or_call record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (attributed_quote record) = 1 /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (routing_inst record) = 4 /\
      Datatypes.length (rout_strategy record) = 6 /\
      Datatypes.length (route_delivery_method record) = 3 /\
      Datatypes.length (ex_destination record) = 1 /\
      Datatypes.length (target_party_id record) = 4 /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      (cmta_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (clearing_optional_data record) = 16 /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (drill_thru_protection record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (equity_party_id record) = 4 /\
      Datatypes.length (client_id_attr record) = 4 /\
      Datatypes.length (frequent_trader_id record) = 6 /\
      Datatypes.length (session_eligibility record) = 1 /\
      Datatypes.length (combo_order record) = 1 /\
      Datatypes.length (compression record) = 1 /\
      Datatypes.length (floor_destination record) = 4 /\
      Datatypes.length (floor_routing_inst record) = 1 /\
      Datatypes.length (order_origin record) = 3 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (strategy_id record) = 1 /\
      Datatypes.length (held record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_bytes 1 (ord_type record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 4 (min_qty record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 16 (account record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_bytes 1 (display_indicator record) ++
      encode_uint 4 (max_floor record) ++
      encode_uint 4 (order_qty record) ++
      PreventMatch.encode (prevent_match record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_bytes 1 (open_close record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 8 (working_price record) ++
      encode_uint 8 (expire_time record) ++
      encode_bytes 1 (attributed_quote record) ++
      encode_uint 8 (stop_px record) ++
      encode_bytes 4 (routing_inst record) ++
      encode_bytes 6 (rout_strategy record) ++
      encode_bytes 3 (route_delivery_method record) ++
      encode_bytes 1 (ex_destination record) ++
      encode_bytes 4 (target_party_id record) ++
      encode_uint 8 (auction_id record) ++
      encode_uint 4 (cmta_number record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 16 (clearing_optional_data record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (drill_thru_protection record) ++
      encode_bytes 4 (equity_party_id record) ++
      encode_bytes 4 (client_id_attr record) ++
      encode_bytes 6 (frequent_trader_id record) ++
      encode_bytes 1 (session_eligibility record) ++
      encode_bytes 1 (combo_order record) ++
      encode_bytes 1 (compression record) ++
      encode_bytes 4 (floor_destination record) ++
      encode_bytes 1 (floor_routing_inst record) ++
      encode_bytes 3 (order_origin record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (strategy_id record) ++
      encode_bytes 1 (held record).

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
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (display_indicator_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (max_floor_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (order_qty_value, bytes) =>
                                                                              match PreventMatch.decode bytes with
                                                                              | None => None
                                                                              | Some (prevent_match_value, bytes) =>
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
                                                                                                  | Some (leaves_qty_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (display_price_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (working_price_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (expire_time_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (attributed_quote_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (stop_px_value, bytes) =>
                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (routing_inst_value, bytes) =>
                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (rout_strategy_value, bytes) =>
                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (route_delivery_method_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ex_destination_value, bytes) =>
                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (target_party_id_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (auction_id_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (cmta_number_value, bytes) =>
                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (routing_firm_id_value, bytes) =>
                                                                                                                                                          match decode_bytes 16 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (clearing_optional_data_value, bytes) =>
                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (cum_qty_value, bytes) =>
                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (drill_thru_protection_value, bytes) =>
                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (equity_party_id_value, bytes) =>
                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (client_id_attr_value, bytes) =>
                                                                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (frequent_trader_id_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (session_eligibility_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (combo_order_value, bytes) =>
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
                                                                                                                                                                                                          | Some (price_type_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (strategy_id_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (held_value, bytes) =>
                                                                                                                                                                                                                      Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; side := side_value; price := price_value; exec_inst := exec_inst_value; ord_type := ord_type_value; time_in_force := time_in_force_value; min_qty := min_qty_value; symbol := symbol_value; capacity := capacity_value; account := account_value; clearing_firm := clearing_firm_value; clearing_account := clearing_account_value; display_indicator := display_indicator_value; max_floor := max_floor_value; order_qty := order_qty_value; prevent_match := prevent_match_value; maturity_date := maturity_date_value; strike_price := strike_price_value; put_or_call := put_or_call_value; open_close := open_close_value; leaves_qty := leaves_qty_value; display_price := display_price_value; working_price := working_price_value; expire_time := expire_time_value; attributed_quote := attributed_quote_value; stop_px := stop_px_value; routing_inst := routing_inst_value; rout_strategy := rout_strategy_value; route_delivery_method := route_delivery_method_value; ex_destination := ex_destination_value; target_party_id := target_party_id_value; auction_id := auction_id_value; cmta_number := cmta_number_value; routing_firm_id := routing_firm_id_value; clearing_optional_data := clearing_optional_data_value; cum_qty := cum_qty_value; drill_thru_protection := drill_thru_protection_value; equity_party_id := equity_party_id_value; client_id_attr := client_id_attr_value; frequent_trader_id := frequent_trader_id_value; session_eligibility := session_eligibility_value; combo_order := combo_order_value; compression := compression_value; floor_destination := floor_destination_value; floor_routing_inst := floor_routing_inst_value; order_origin := order_origin_value; price_type := price_type_value; strategy_id := strategy_id_value; held := held_value |}, bytes)
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 240.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !PreventMatch.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 bound_51]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite PreventMatch.decode_encode by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_bytes by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply PreventMatch.eq_dec]. Defined.

  End CarriedRestatementMessage.

  Module DoneForDayMessage.

    (** The Done For Day messages represent orders persisted during the current day session to carry over to the next session *)
    Record t := {
      in_flight : N;
      transaction_time : N;
      cl_ord_id : list byte;
      clearing_firm : list byte;
      routing_firm_id : list byte;
      symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (in_flight record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (clearing_firm record) = 4 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (symbol record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (in_flight record) ++
      encode_uint 8 (transaction_time record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 4 (clearing_firm record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 8 (symbol record).

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
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (routing_firm_id_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              Some ({| in_flight := in_flight_value; transaction_time := transaction_time_value; cl_ord_id := cl_ord_id_value; clearing_firm := clearing_firm_value; routing_firm_id := routing_firm_id_value; symbol := symbol_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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

  End DoneForDayMessage.

End C2OptionsBinaryOrderEntryV1010Exchange.
