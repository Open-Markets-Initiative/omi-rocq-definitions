From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Euronext Drop Copy Gateway

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
      - a field read in bits
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module EuronextOptiqDropCopyGatewayV556.

  Module FrameHeader.

    (** Optiq length prefix, read before the message it frames *)
    Record t := {
      frame : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (frame record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (frame record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (frame_value, bytes) =>
          Some ({| frame := frame_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint_le by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End FrameHeader.

  Module MessageHeader.

    (** Optiq Sbe message header — message identifiers and length of message root *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (block_length record) ++
      encode_uint_le 2 (template_id record) ++
      encode_uint_le 2 (schema_id record) ++
      encode_uint_le 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module DcPriceUpdateMessage.

    (** DCPriceUpdateMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      emm : N;
      event_id : N;
      event_time : N;
      price_type : N;
      symbol_index : N;
      price_optional : N;
      quantity_optional : N;
      imbalance_qty : N;
      imbalance_qty_side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (event_time record < 256 ^ N.of_nat 8)%N /\
      (price_type record < 256 ^ N.of_nat 1)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (quantity_optional record < 256 ^ N.of_nat 8)%N /\
      (imbalance_qty record < 256 ^ N.of_nat 8)%N /\
      (imbalance_qty_side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint_le 8 (event_time record) ++
      encode_uint 1 (price_type record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (price_optional record) ++
      encode_uint_le 8 (quantity_optional record) ++
      encode_uint_le 8 (imbalance_qty record) ++
      encode_uint 1 (imbalance_qty_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (emm_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (event_id_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (event_time_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (price_type_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (symbol_index_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (price_optional_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (quantity_optional_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (imbalance_qty_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (imbalance_qty_side_value, bytes) =>
                                                      Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; emm := emm_value; event_id := event_id_value; event_time := event_time_value; price_type := price_type_value; symbol_index := symbol_index_value; price_optional := price_optional_value; quantity_optional := quantity_optional_value; imbalance_qty := imbalance_qty_value; imbalance_qty_side := imbalance_qty_side_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End DcPriceUpdateMessage.

  Module GroupSizeEncoding.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GroupSizeEncoding.

  Module DcShortTradeCancellationMessage.

    (** DCShortTradeCancellationMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      execution_id : N;
      emm : N;
      event_id : N;
      symbol_index : N;
      book_in : N;
      last_traded_px : N;
      last_shares : N;
      trade_unique_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (last_traded_px record < 256 ^ N.of_nat 8)%N /\
      (last_shares record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_unique_identifier record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 4 (execution_id record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (last_traded_px record) ++
      encode_uint_le 8 (last_shares record) ++
      encode_bytes 16 (trade_unique_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (execution_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (emm_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (event_id_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (symbol_index_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (book_in_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (last_traded_px_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (last_shares_value, bytes) =>
                                              match decode_bytes 16 bytes with
                                              | None => None
                                              | Some (trade_unique_identifier_value, bytes) =>
                                                  Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; execution_id := execution_id_value; emm := emm_value; event_id := event_id_value; symbol_index := symbol_index_value; book_in := book_in_value; last_traded_px := last_traded_px_value; last_shares := last_shares_value; trade_unique_identifier := trade_unique_identifier_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 77.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcShortTradeCancellationMessage.

  Module DcafqrfeMessage.

    (** DCAFQRFEMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      afq_reason : N;
      book_out_time : N;
      emm : N;
      event_id : N;
      symbol_index : N;
      firm_id : list byte;
      afq_indicator : N;
      oe_session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (afq_reason record < 256 ^ N.of_nat 1)%N /\
      (book_out_time record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (afq_indicator record < 256 ^ N.of_nat 1)%N /\
      (oe_session_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint 1 (afq_reason record) ++
      encode_uint_le 8 (book_out_time record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint 1 (afq_indicator record) ++
      encode_uint_le 8 (oe_session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (afq_reason_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (book_out_time_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (emm_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (event_id_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (symbol_index_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (firm_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (afq_indicator_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (oe_session_id_value, bytes) =>
                                                  Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; afq_reason := afq_reason_value; book_out_time := book_out_time_value; emm := emm_value; event_id := event_id_value; symbol_index := symbol_index_value; firm_id := firm_id_value; afq_indicator := afq_indicator_value; oe_session_id := oe_session_id_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcafqrfeMessage.

  Module DcDeclarationNewMessage.

    (** DCDeclarationNewMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      message_sending_time : N;
      book_in : N;
      book_out_time : N;
      oegin_from_member : N;
      oegout_time_to_me : N;
      event_id : N;
      declaration_event_type : N;
      firm_id : list byte;
      oe_session_id : N;
      account_type : N;
      client_order_id : N;
      emm : N;
      declaration_id : N;
      declaration_status : N;
      price_optional : N;
      quantity_optional : N;
      side : N;
      symbol_index : N;
      operation_type : N;
      cross_order_indicator : N;
      entering_counterparty : list byte;
      trader_id : list byte;
      investor_id : list byte;
      free_text : list byte;
      principal_code : list byte;
      clearing_firm_id_optional : list byte;
      clearing_account : list byte;
      settlement_period : N;
      settlement_flag : N;
      guarantee_flag : N;
      transaction_price_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (message_sending_time record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time record < 256 ^ N.of_nat 8)%N /\
      (oegin_from_member record < 256 ^ N.of_nat 8)%N /\
      (oegout_time_to_me record < 256 ^ N.of_nat 8)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (declaration_event_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (oe_session_id record < 256 ^ N.of_nat 8)%N /\
      (account_type record < 256 ^ N.of_nat 1)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (declaration_id record < 256 ^ N.of_nat 8)%N /\
      (declaration_status record < 256 ^ N.of_nat 1)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (quantity_optional record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (operation_type record < 256 ^ N.of_nat 1)%N /\
      (cross_order_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (entering_counterparty record) = 8 /\
      Datatypes.length (trader_id record) = 16 /\
      Datatypes.length (investor_id record) = 16 /\
      Datatypes.length (free_text record) = 18 /\
      Datatypes.length (principal_code record) = 8 /\
      Datatypes.length (clearing_firm_id_optional record) = 8 /\
      Datatypes.length (clearing_account record) = 16 /\
      (settlement_period record < 256 ^ N.of_nat 1)%N /\
      (settlement_flag record < 256 ^ N.of_nat 1)%N /\
      (guarantee_flag record < 256 ^ N.of_nat 1)%N /\
      (transaction_price_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 8 (message_sending_time record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time record) ++
      encode_uint_le 8 (oegin_from_member record) ++
      encode_uint_le 8 (oegout_time_to_me record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint 1 (declaration_event_type record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (oe_session_id record) ++
      encode_uint 1 (account_type record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (declaration_id record) ++
      encode_uint 1 (declaration_status record) ++
      encode_uint_le 8 (price_optional record) ++
      encode_uint_le 8 (quantity_optional record) ++
      encode_uint 1 (side record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (operation_type record) ++
      encode_uint 1 (cross_order_indicator record) ++
      encode_bytes 8 (entering_counterparty record) ++
      encode_bytes 16 (trader_id record) ++
      encode_bytes 16 (investor_id record) ++
      encode_bytes 18 (free_text record) ++
      encode_bytes 8 (principal_code record) ++
      encode_bytes 8 (clearing_firm_id_optional record) ++
      encode_bytes 16 (clearing_account record) ++
      encode_uint 1 (settlement_period record) ++
      encode_uint 1 (settlement_flag record) ++
      encode_uint 1 (guarantee_flag record) ++
      encode_uint 1 (transaction_price_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (message_sending_time_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (book_in_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (book_out_time_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (oegin_from_member_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (oegout_time_to_me_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (event_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (declaration_event_type_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (firm_id_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (oe_session_id_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (account_type_value, bytes) =>
                                                          match decode_uint_le 8 bytes with
                                                          | None => None
                                                          | Some (client_order_id_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (emm_value, bytes) =>
                                                                  match decode_uint_le 8 bytes with
                                                                  | None => None
                                                                  | Some (declaration_id_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (declaration_status_value, bytes) =>
                                                                          match decode_uint_le 8 bytes with
                                                                          | None => None
                                                                          | Some (price_optional_value, bytes) =>
                                                                              match decode_uint_le 8 bytes with
                                                                              | None => None
                                                                              | Some (quantity_optional_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (side_value, bytes) =>
                                                                                      match decode_uint_le 4 bytes with
                                                                                      | None => None
                                                                                      | Some (symbol_index_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (operation_type_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (cross_order_indicator_value, bytes) =>
                                                                                                  match decode_bytes 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (entering_counterparty_value, bytes) =>
                                                                                                      match decode_bytes 16 bytes with
                                                                                                      | None => None
                                                                                                      | Some (trader_id_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (investor_id_value, bytes) =>
                                                                                                              match decode_bytes 18 bytes with
                                                                                                              | None => None
                                                                                                              | Some (free_text_value, bytes) =>
                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (principal_code_value, bytes) =>
                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (clearing_firm_id_optional_value, bytes) =>
                                                                                                                          match decode_bytes 16 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (clearing_account_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (settlement_period_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (settlement_flag_value, bytes) =>
                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (guarantee_flag_value, bytes) =>
                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (transaction_price_type_value, bytes) =>
                                                                                                                                              Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; message_sending_time := message_sending_time_value; book_in := book_in_value; book_out_time := book_out_time_value; oegin_from_member := oegin_from_member_value; oegout_time_to_me := oegout_time_to_me_value; event_id := event_id_value; declaration_event_type := declaration_event_type_value; firm_id := firm_id_value; oe_session_id := oe_session_id_value; account_type := account_type_value; client_order_id := client_order_id_value; emm := emm_value; declaration_id := declaration_id_value; declaration_status := declaration_status_value; price_optional := price_optional_value; quantity_optional := quantity_optional_value; side := side_value; symbol_index := symbol_index_value; operation_type := operation_type_value; cross_order_indicator := cross_order_indicator_value; entering_counterparty := entering_counterparty_value; trader_id := trader_id_value; investor_id := investor_id_value; free_text := free_text_value; principal_code := principal_code_value; clearing_firm_id_optional := clearing_firm_id_optional_value; clearing_account := clearing_account_value; settlement_period := settlement_period_value; settlement_flag := settlement_flag_value; guarantee_flag := guarantee_flag_value; transaction_price_type := transaction_price_type_value |}, bytes)
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 221.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      rewrite decode_encode_uint_le by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint_le by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcDeclarationNewMessage.

  Module DcShortDeclarationRejectMessage.

    (** DCShortDeclarationRejectMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      message_sending_time : N;
      book_in : N;
      book_out_time : N;
      oegin_from_member : N;
      oegout_time_to_me : N;
      event_id : N;
      declaration_event_type : N;
      firm_id : list byte;
      client_order_id : N;
      emm : N;
      declaration_id : N;
      symbol_index : N;
      error_code : N;
      rejected_message_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (message_sending_time record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time record < 256 ^ N.of_nat 8)%N /\
      (oegin_from_member record < 256 ^ N.of_nat 8)%N /\
      (oegout_time_to_me record < 256 ^ N.of_nat 8)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (declaration_event_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (declaration_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (rejected_message_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 8 (message_sending_time record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time record) ++
      encode_uint_le 8 (oegin_from_member record) ++
      encode_uint_le 8 (oegout_time_to_me record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint 1 (declaration_event_type record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (declaration_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 2 (error_code record) ++
      encode_uint_le 2 (rejected_message_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (message_sending_time_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (book_in_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (book_out_time_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (oegin_from_member_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (oegout_time_to_me_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (event_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (declaration_event_type_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (firm_id_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (client_order_id_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (emm_value, bytes) =>
                                                          match decode_uint_le 8 bytes with
                                                          | None => None
                                                          | Some (declaration_id_value, bytes) =>
                                                              match decode_uint_le 4 bytes with
                                                              | None => None
                                                              | Some (symbol_index_value, bytes) =>
                                                                  match decode_uint_le 2 bytes with
                                                                  | None => None
                                                                  | Some (error_code_value, bytes) =>
                                                                      match decode_uint_le 2 bytes with
                                                                      | None => None
                                                                      | Some (rejected_message_id_value, bytes) =>
                                                                          Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; message_sending_time := message_sending_time_value; book_in := book_in_value; book_out_time := book_out_time_value; oegin_from_member := oegin_from_member_value; oegout_time_to_me := oegout_time_to_me_value; event_id := event_id_value; declaration_event_type := declaration_event_type_value; firm_id := firm_id_value; client_order_id := client_order_id_value; emm := emm_value; declaration_id := declaration_id_value; symbol_index := symbol_index_value; error_code := error_code_value; rejected_message_id := rejected_message_id_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 102.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcShortDeclarationRejectMessage.

  Module DcShortDeclarationCancelMessage.

    (** DCShortDeclarationCancelMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      message_sending_time : N;
      book_in : N;
      book_out_time : N;
      oegin_from_member : N;
      oegout_time_to_me : N;
      event_id : N;
      declaration_event_type : N;
      firm_id : list byte;
      oe_session_id : N;
      client_order_id : N;
      emm : N;
      declaration_id : N;
      symbol_index : N;
      declaration_kill_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (message_sending_time record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time record < 256 ^ N.of_nat 8)%N /\
      (oegin_from_member record < 256 ^ N.of_nat 8)%N /\
      (oegout_time_to_me record < 256 ^ N.of_nat 8)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (declaration_event_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (oe_session_id record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (declaration_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (declaration_kill_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 8 (message_sending_time record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time record) ++
      encode_uint_le 8 (oegin_from_member record) ++
      encode_uint_le 8 (oegout_time_to_me record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint 1 (declaration_event_type record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (oe_session_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (declaration_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (declaration_kill_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (message_sending_time_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (book_in_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (book_out_time_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (oegin_from_member_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (oegout_time_to_me_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (event_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (declaration_event_type_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (firm_id_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (oe_session_id_value, bytes) =>
                                                      match decode_uint_le 8 bytes with
                                                      | None => None
                                                      | Some (client_order_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (emm_value, bytes) =>
                                                              match decode_uint_le 8 bytes with
                                                              | None => None
                                                              | Some (declaration_id_value, bytes) =>
                                                                  match decode_uint_le 4 bytes with
                                                                  | None => None
                                                                  | Some (symbol_index_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (declaration_kill_reason_value, bytes) =>
                                                                          Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; message_sending_time := message_sending_time_value; book_in := book_in_value; book_out_time := book_out_time_value; oegin_from_member := oegin_from_member_value; oegout_time_to_me := oegout_time_to_me_value; event_id := event_id_value; declaration_event_type := declaration_event_type_value; firm_id := firm_id_value; oe_session_id := oe_session_id_value; client_order_id := client_order_id_value; emm := emm_value; declaration_id := declaration_id_value; symbol_index := symbol_index_value; declaration_kill_reason := declaration_kill_reason_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 107.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcShortDeclarationCancelMessage.

  Module DcShortTradeDeclarationCancellationMessage.

    (** DCShortTradeDeclarationCancellationMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      book_in : N;
      event_id : N;
      emm : N;
      execution_id : N;
      symbol_index : N;
      price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (execution_id record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 4 (execution_id record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (book_in_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (event_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (emm_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (symbol_index_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (quantity_value, bytes) =>
                                              Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; book_in := book_in_value; event_id := event_id_value; emm := emm_value; execution_id := execution_id_value; symbol_index := symbol_index_value; price := price_value; quantity := quantity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End DcShortTradeDeclarationCancellationMessage.

  Module DcTradeBustDeclarationMessage.

    (** DCTradeBustDeclarationMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      message_sending_time : N;
      book_in : N;
      book_out_time : N;
      oegin_from_member : N;
      oegout_time_to_me : N;
      event_id : N;
      declaration_event_type : N;
      firm_id : list byte;
      oe_session_id : N;
      account_type : N;
      client_order_id : N;
      emm : N;
      declaration_id : N;
      declaration_status : N;
      price_optional : N;
      quantity_optional : N;
      side : N;
      symbol_index : N;
      operation_type : N;
      entering_counterparty : list byte;
      trader_id : list byte;
      investor_id : list byte;
      free_text : list byte;
      clearing_firm_id_optional : list byte;
      clearing_account : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (message_sending_time record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time record < 256 ^ N.of_nat 8)%N /\
      (oegin_from_member record < 256 ^ N.of_nat 8)%N /\
      (oegout_time_to_me record < 256 ^ N.of_nat 8)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (declaration_event_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (oe_session_id record < 256 ^ N.of_nat 8)%N /\
      (account_type record < 256 ^ N.of_nat 1)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (declaration_id record < 256 ^ N.of_nat 8)%N /\
      (declaration_status record < 256 ^ N.of_nat 1)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (quantity_optional record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (operation_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (entering_counterparty record) = 8 /\
      Datatypes.length (trader_id record) = 16 /\
      Datatypes.length (investor_id record) = 16 /\
      Datatypes.length (free_text record) = 18 /\
      Datatypes.length (clearing_firm_id_optional record) = 8 /\
      Datatypes.length (clearing_account record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 8 (message_sending_time record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time record) ++
      encode_uint_le 8 (oegin_from_member record) ++
      encode_uint_le 8 (oegout_time_to_me record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint 1 (declaration_event_type record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 8 (oe_session_id record) ++
      encode_uint 1 (account_type record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (declaration_id record) ++
      encode_uint 1 (declaration_status record) ++
      encode_uint_le 8 (price_optional record) ++
      encode_uint_le 8 (quantity_optional record) ++
      encode_uint 1 (side record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (operation_type record) ++
      encode_bytes 8 (entering_counterparty record) ++
      encode_bytes 16 (trader_id record) ++
      encode_bytes 16 (investor_id record) ++
      encode_bytes 18 (free_text record) ++
      encode_bytes 8 (clearing_firm_id_optional record) ++
      encode_bytes 16 (clearing_account record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (message_sending_time_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (book_in_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (book_out_time_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (oegin_from_member_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (oegout_time_to_me_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (event_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (declaration_event_type_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (firm_id_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (oe_session_id_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (account_type_value, bytes) =>
                                                          match decode_uint_le 8 bytes with
                                                          | None => None
                                                          | Some (client_order_id_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (emm_value, bytes) =>
                                                                  match decode_uint_le 8 bytes with
                                                                  | None => None
                                                                  | Some (declaration_id_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (declaration_status_value, bytes) =>
                                                                          match decode_uint_le 8 bytes with
                                                                          | None => None
                                                                          | Some (price_optional_value, bytes) =>
                                                                              match decode_uint_le 8 bytes with
                                                                              | None => None
                                                                              | Some (quantity_optional_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (side_value, bytes) =>
                                                                                      match decode_uint_le 4 bytes with
                                                                                      | None => None
                                                                                      | Some (symbol_index_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (operation_type_value, bytes) =>
                                                                                              match decode_bytes 8 bytes with
                                                                                              | None => None
                                                                                              | Some (entering_counterparty_value, bytes) =>
                                                                                                  match decode_bytes 16 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trader_id_value, bytes) =>
                                                                                                      match decode_bytes 16 bytes with
                                                                                                      | None => None
                                                                                                      | Some (investor_id_value, bytes) =>
                                                                                                          match decode_bytes 18 bytes with
                                                                                                          | None => None
                                                                                                          | Some (free_text_value, bytes) =>
                                                                                                              match decode_bytes 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (clearing_firm_id_optional_value, bytes) =>
                                                                                                                  match decode_bytes 16 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (clearing_account_value, bytes) =>
                                                                                                                      Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; message_sending_time := message_sending_time_value; book_in := book_in_value; book_out_time := book_out_time_value; oegin_from_member := oegin_from_member_value; oegout_time_to_me := oegout_time_to_me_value; event_id := event_id_value; declaration_event_type := declaration_event_type_value; firm_id := firm_id_value; oe_session_id := oe_session_id_value; account_type := account_type_value; client_order_id := client_order_id_value; emm := emm_value; declaration_id := declaration_id_value; declaration_status := declaration_status_value; price_optional := price_optional_value; quantity_optional := quantity_optional_value; side := side_value; symbol_index := symbol_index_value; operation_type := operation_type_value; entering_counterparty := entering_counterparty_value; trader_id := trader_id_value; investor_id := investor_id_value; free_text := free_text_value; clearing_firm_id_optional := clearing_firm_id_optional_value; clearing_account := clearing_account_value |}, bytes)
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 208.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      rewrite decode_encode_uint_le by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint_le by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcTradeBustDeclarationMessage.

  Module DcShortDeclarationFillMessage.

    (** DCShortDeclarationFillMessage *)
    Record t := {
      msg_seq_num : N;
      produce_time : N;
      consume_time : N;
      message_sending_time : N;
      book_in : N;
      book_out_time : N;
      oegin_from_member : N;
      oegout_time_to_me : N;
      operation_type : N;
      declaration_event_type : N;
      declaration_status : N;
      event_id : N;
      emm : N;
      symbol_index : N;
      declaration_id : N;
      price : N;
      quantity : N;
      side : N;
      cross_order_indicator : N;
      trade_time : N;
      entering_counterparty : list byte;
      session_optional : N;
      trade_type : N;
      firm_id : list byte;
      oe_partition_id : N;
      logical_access_id : N;
      trader_id : list byte;
      investor_id : list byte;
      principal_code : list byte;
      clearing_firm_id_optional : list byte;
      clearing_account : list byte;
      account_type : N;
      client_order_id : N;
      free_text : list byte;
      settlement_period_optional : N;
      settlement_flag_optional : N;
      guarantee_flag_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (message_sending_time record < 256 ^ N.of_nat 8)%N /\
      (book_in record < 256 ^ N.of_nat 8)%N /\
      (book_out_time record < 256 ^ N.of_nat 8)%N /\
      (oegin_from_member record < 256 ^ N.of_nat 8)%N /\
      (oegout_time_to_me record < 256 ^ N.of_nat 8)%N /\
      (operation_type record < 256 ^ N.of_nat 1)%N /\
      (declaration_event_type record < 256 ^ N.of_nat 1)%N /\
      (declaration_status record < 256 ^ N.of_nat 1)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (declaration_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (cross_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (entering_counterparty record) = 8 /\
      (session_optional record < 256 ^ N.of_nat 1)%N /\
      (trade_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm_id record) = 8 /\
      (oe_partition_id record < 256 ^ N.of_nat 2)%N /\
      (logical_access_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trader_id record) = 16 /\
      Datatypes.length (investor_id record) = 16 /\
      Datatypes.length (principal_code record) = 8 /\
      Datatypes.length (clearing_firm_id_optional record) = 8 /\
      Datatypes.length (clearing_account record) = 16 /\
      (account_type record < 256 ^ N.of_nat 1)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (free_text record) = 18 /\
      (settlement_period_optional record < 256 ^ N.of_nat 1)%N /\
      (settlement_flag_optional record < 256 ^ N.of_nat 1)%N /\
      (guarantee_flag_optional record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (msg_seq_num record) ++
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 8 (message_sending_time record) ++
      encode_uint_le 8 (book_in record) ++
      encode_uint_le 8 (book_out_time record) ++
      encode_uint_le 8 (oegin_from_member record) ++
      encode_uint_le 8 (oegout_time_to_me record) ++
      encode_uint 1 (operation_type record) ++
      encode_uint 1 (declaration_event_type record) ++
      encode_uint 1 (declaration_status record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (declaration_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 8 (quantity record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (cross_order_indicator record) ++
      encode_uint_le 8 (trade_time record) ++
      encode_bytes 8 (entering_counterparty record) ++
      encode_uint 1 (session_optional record) ++
      encode_uint 1 (trade_type record) ++
      encode_bytes 8 (firm_id record) ++
      encode_uint_le 2 (oe_partition_id record) ++
      encode_uint_le 4 (logical_access_id record) ++
      encode_bytes 16 (trader_id record) ++
      encode_bytes 16 (investor_id record) ++
      encode_bytes 8 (principal_code record) ++
      encode_bytes 8 (clearing_firm_id_optional record) ++
      encode_bytes 16 (clearing_account record) ++
      encode_uint 1 (account_type record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_bytes 18 (free_text record) ++
      encode_uint 1 (settlement_period_optional record) ++
      encode_uint 1 (settlement_flag_optional record) ++
      encode_uint 1 (guarantee_flag_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (msg_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (produce_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (consume_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (message_sending_time_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (book_in_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (book_out_time_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (oegin_from_member_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (oegout_time_to_me_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (operation_type_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (declaration_event_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (declaration_status_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (event_id_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (emm_value, bytes) =>
                                                          match decode_uint_le 4 bytes with
                                                          | None => None
                                                          | Some (symbol_index_value, bytes) =>
                                                              match decode_uint_le 8 bytes with
                                                              | None => None
                                                              | Some (declaration_id_value, bytes) =>
                                                                  match decode_uint_le 8 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint_le 8 bytes with
                                                                      | None => None
                                                                      | Some (quantity_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (side_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (cross_order_indicator_value, bytes) =>
                                                                                  match decode_uint_le 8 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_time_value, bytes) =>
                                                                                      match decode_bytes 8 bytes with
                                                                                      | None => None
                                                                                      | Some (entering_counterparty_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (session_optional_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (trade_type_value, bytes) =>
                                                                                                  match decode_bytes 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (firm_id_value, bytes) =>
                                                                                                      match decode_uint_le 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (oe_partition_id_value, bytes) =>
                                                                                                          match decode_uint_le 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (logical_access_id_value, bytes) =>
                                                                                                              match decode_bytes 16 bytes with
                                                                                                              | None => None
                                                                                                              | Some (trader_id_value, bytes) =>
                                                                                                                  match decode_bytes 16 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (investor_id_value, bytes) =>
                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (principal_code_value, bytes) =>
                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (clearing_firm_id_optional_value, bytes) =>
                                                                                                                              match decode_bytes 16 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (clearing_account_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (account_type_value, bytes) =>
                                                                                                                                      match decode_uint_le 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (client_order_id_value, bytes) =>
                                                                                                                                          match decode_bytes 18 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (free_text_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (settlement_period_optional_value, bytes) =>
                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (settlement_flag_optional_value, bytes) =>
                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (guarantee_flag_optional_value, bytes) =>
                                                                                                                                                          Some ({| msg_seq_num := msg_seq_num_value; produce_time := produce_time_value; consume_time := consume_time_value; message_sending_time := message_sending_time_value; book_in := book_in_value; book_out_time := book_out_time_value; oegin_from_member := oegin_from_member_value; oegout_time_to_me := oegout_time_to_me_value; operation_type := operation_type_value; declaration_event_type := declaration_event_type_value; declaration_status := declaration_status_value; event_id := event_id_value; emm := emm_value; symbol_index := symbol_index_value; declaration_id := declaration_id_value; price := price_value; quantity := quantity_value; side := side_value; cross_order_indicator := cross_order_indicator_value; trade_time := trade_time_value; entering_counterparty := entering_counterparty_value; session_optional := session_optional_value; trade_type := trade_type_value; firm_id := firm_id_value; oe_partition_id := oe_partition_id_value; logical_access_id := logical_access_id_value; trader_id := trader_id_value; investor_id := investor_id_value; principal_code := principal_code_value; clearing_firm_id_optional := clearing_firm_id_optional_value; clearing_account := clearing_account_value; account_type := account_type_value; client_order_id := client_order_id_value; free_text := free_text_value; settlement_period_optional := settlement_period_optional_value; settlement_flag_optional := settlement_flag_optional_value; guarantee_flag_optional := guarantee_flag_optional_value |}, bytes)
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 228.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 bound_36]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint_le by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint_le by exact bound_24.
      rewrite decode_encode_uint_le by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint_le by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcShortDeclarationFillMessage.

  Module DcClearBookMessage.

    (** DCClearBookMessage *)
    Record t := {
      produce_time : N;
      consume_time : N;
      sequence_time : N;
      book_in_time : N;
      symbol_index : N;
      emm : N;
      clear_book_origin : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (produce_time record < 256 ^ N.of_nat 8)%N /\
      (consume_time record < 256 ^ N.of_nat 8)%N /\
      (sequence_time record < 256 ^ N.of_nat 8)%N /\
      (book_in_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (clear_book_origin record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (produce_time record) ++
      encode_uint_le 8 (consume_time record) ++
      encode_uint_le 8 (sequence_time record) ++
      encode_uint_le 8 (book_in_time record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint 1 (emm record) ++
      encode_uint 1 (clear_book_origin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (produce_time_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (consume_time_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (sequence_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (book_in_time_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (symbol_index_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (emm_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (clear_book_origin_value, bytes) =>
                                  Some ({| produce_time := produce_time_value; consume_time := consume_time_value; sequence_time := sequence_time_value; book_in_time := book_in_time_value; symbol_index := symbol_index_value; emm := emm_value; clear_book_origin := clear_book_origin_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End DcClearBookMessage.

End EuronextOptiqDropCopyGatewayV556.
