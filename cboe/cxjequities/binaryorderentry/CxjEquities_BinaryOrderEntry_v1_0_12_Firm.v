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

Module CxjEquitiesBinaryOrderEntryV1012Firm.

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

  Module NewOrderJpEquitiesV1.

    (** Submission of a new order to Cboe Japan *)
    Record t := {
      account : list byte;
      trading_firm : list byte;
      cl_ord_id : list byte;
      order_qty : N;
      ord_type : list byte;
      price : N;
      capacity : list byte;
      side : list byte;
      symbol : list byte;
      time_in_force : list byte;
      expire_time : N;
      cash_margin : list byte;
      risk_group_id : N;
      no_trade_feat : list byte;
      no_trade_key : list byte;
      posting_instruction : list byte;
      order_classification : list byte;
      margin_transaction_type : list byte;
      company_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (account record) = 10 /\
      Datatypes.length (trading_firm record) = 4 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (time_in_force record) = 1 /\
      (expire_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cash_margin record) = 1 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (no_trade_feat record) = 1 /\
      Datatypes.length (no_trade_key record) = 10 /\
      Datatypes.length (posting_instruction record) = 1 /\
      Datatypes.length (order_classification record) = 1 /\
      Datatypes.length (margin_transaction_type record) = 1 /\
      Datatypes.length (company_id record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (account record) ++
      encode_bytes 4 (trading_firm record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 8 (expire_time record) ++
      encode_bytes 1 (cash_margin record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_bytes 1 (no_trade_feat record) ++
      encode_bytes 10 (no_trade_key record) ++
      encode_bytes 1 (posting_instruction record) ++
      encode_bytes 1 (order_classification record) ++
      encode_bytes 1 (margin_transaction_type record) ++
      encode_bytes 4 (company_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (account_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (trading_firm_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
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
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (symbol_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (time_in_force_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (expire_time_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (cash_margin_value, bytes) =>
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
                                                                  | Some (posting_instruction_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (order_classification_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (margin_transaction_type_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (company_id_value, bytes) =>
                                                                                  Some ({| account := account_value; trading_firm := trading_firm_value; cl_ord_id := cl_ord_id_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; capacity := capacity_value; side := side_value; symbol := symbol_value; time_in_force := time_in_force_value; expire_time := expire_time_value; cash_margin := cash_margin_value; risk_group_id := risk_group_id_value; no_trade_feat := no_trade_feat_value; no_trade_key := no_trade_key_value; posting_instruction := posting_instruction_value; order_classification := order_classification_value; margin_transaction_type := margin_transaction_type_value; company_id := company_id_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 87.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderJpEquitiesV1.

  Module ModifyOrderJpEquitiesV1.

    (** Request to modify an order. Only Price and OrderQty may be adjusted *)
    Record t := {
      trading_firm : list byte;
      cl_ord_id : list byte;
      order_qty : N;
      orig_cl_ord_id : list byte;
      price : N;
      cancel_orig_on_reject : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_firm record) = 4 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cancel_orig_on_reject record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (trading_firm record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (cancel_orig_on_reject record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (trading_firm_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_qty_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cancel_orig_on_reject_value, bytes) =>
                              Some ({| trading_firm := trading_firm_value; cl_ord_id := cl_ord_id_value; order_qty := order_qty_value; orig_cl_ord_id := orig_cl_ord_id_value; price := price_value; cancel_orig_on_reject := cancel_orig_on_reject_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderJpEquitiesV1.

  Module CancelOrderJpEquitiesV1.

    (** Request to cancel a single order *)
    Record t := {
      trading_firm : list byte;
      orig_cl_ord_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_firm record) = 4 /\
      Datatypes.length (orig_cl_ord_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (trading_firm record) ++
      encode_bytes 20 (orig_cl_ord_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (trading_firm_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (orig_cl_ord_id_value, bytes) =>
              Some ({| trading_firm := trading_firm_value; orig_cl_ord_id := orig_cl_ord_id_value |}, bytes)
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

  End CancelOrderJpEquitiesV1.

End CxjEquitiesBinaryOrderEntryV1012Firm.
