From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Investors Exchange Binary Order Entry

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
      - the dispatch that chooses a message by its type
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module IexOptionsBinaryOrderEntryV103Client.

  Module MessageHeader.

    (** Iex Options Sbe message header — message identifiers and length of message root *)
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

  Module LoginRequestMessage.

    (** LoginRequestMessage *)
    Record t := {
      logon_id : list byte;
      token : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (logon_id record) = 16 /\
      Datatypes.length (token record) = 32.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (logon_id record) ++
      encode_bytes 32 (token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (logon_id_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (token_value, bytes) =>
              Some ({| logon_id := logon_id_value; token := token_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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

  End LoginRequestMessage.

  Module SequencedMessageHeaderMessage.

    (** SequencedMessageHeaderMessage *)
    Record t := {
      subsession_id : N;
      sequence : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (subsession_id record < 256 ^ N.of_nat 8)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (subsession_id record) ++
      encode_uint_le 4 (sequence record) ++
      encode_uint_le 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (subsession_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (sequence_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  Some ({| subsession_id := subsession_id_value; sequence := sequence_value; timestamp := timestamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SequencedMessageHeaderMessage.

  Module SubsessionJoinMessage.

    (** SubsessionJoinMessage *)
    Record t := {
      subsession_id : N;
      start_sequence : N;
      end_sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (subsession_id record < 256 ^ N.of_nat 8)%N /\
      (start_sequence record < 256 ^ N.of_nat 4)%N /\
      (end_sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (subsession_id record) ++
      encode_uint_le 4 (start_sequence record) ++
      encode_uint_le 4 (end_sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (subsession_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (start_sequence_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (end_sequence_value, bytes) =>
                  Some ({| subsession_id := subsession_id_value; start_sequence := start_sequence_value; end_sequence := end_sequence_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SubsessionJoinMessage.

  Module SubsessionLeaveMessage.

    (** SubsessionLeaveMessage *)
    Record t := {
      subsession_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (subsession_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (subsession_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (subsession_id_value, bytes) =>
          Some ({| subsession_id := subsession_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End SubsessionLeaveMessage.

  Module NewOrderSingleMessage.

    (** NewOrderSingleMessage *)
    Record t := {
      account_account_optional : list byte;
      instrument_id : N;
      market_participant_id_optional : list byte;
      cl_ord_id : N;
      clearing_account_optional : list byte;
      customer_or_firm : N;
      open_close : N;
      attributed_quote_optional : N;
      time_in_force : N;
      cancel_instead_of_slide_optional : N;
      display_inst : N;
      exec_inst : N;
      ord_type : N;
      target_party_id : list byte;
      auction_id : N;
      clearing_firm : N;
      optional_data : list byte;
      routing_firm_id : list byte;
      aiq : list byte;
      side : N;
      price_price_8_optional : N;
      order_qty_quantity_non_zero : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (account_account_optional record) = 16 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id_optional record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_account_optional record) = 4 /\
      (customer_or_firm record < 256 ^ N.of_nat 1)%N /\
      (open_close record < 256 ^ N.of_nat 1)%N /\
      (attributed_quote_optional record < 256 ^ N.of_nat 1)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (cancel_instead_of_slide_optional record < 256 ^ N.of_nat 1)%N /\
      (display_inst record < 256 ^ N.of_nat 1)%N /\
      (exec_inst record < 256 ^ N.of_nat 1)%N /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (target_party_id record) = 4 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (clearing_firm record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (optional_data record) = 16 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (aiq record) = 3 /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (price_price_8_optional record < 256 ^ N.of_nat 8)%N /\
      (order_qty_quantity_non_zero record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (account_account_optional record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id_optional record) ++
      encode_uint_le 8 (cl_ord_id record) ++
      encode_bytes 4 (clearing_account_optional record) ++
      encode_uint 1 (customer_or_firm record) ++
      encode_uint 1 (open_close record) ++
      encode_uint 1 (attributed_quote_optional record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (cancel_instead_of_slide_optional record) ++
      encode_uint 1 (display_inst record) ++
      encode_uint 1 (exec_inst record) ++
      encode_uint 1 (ord_type record) ++
      encode_bytes 4 (target_party_id record) ++
      encode_uint_le 4 (auction_id record) ++
      encode_uint_le 4 (clearing_firm record) ++
      encode_bytes 16 (optional_data record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 3 (aiq record) ++
      encode_uint 1 (side record) ++
      encode_uint_le 8 (price_price_8_optional record) ++
      encode_uint_le 4 (order_qty_quantity_non_zero record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (account_account_optional_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_optional_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (clearing_account_optional_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (customer_or_firm_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (open_close_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (attributed_quote_optional_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (time_in_force_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (cancel_instead_of_slide_optional_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (display_inst_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (exec_inst_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (ord_type_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (target_party_id_value, bytes) =>
                                                              match decode_uint_le 4 bytes with
                                                              | None => None
                                                              | Some (auction_id_value, bytes) =>
                                                                  match decode_uint_le 4 bytes with
                                                                  | None => None
                                                                  | Some (clearing_firm_value, bytes) =>
                                                                      match decode_bytes 16 bytes with
                                                                      | None => None
                                                                      | Some (optional_data_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (routing_firm_id_value, bytes) =>
                                                                              match decode_bytes 3 bytes with
                                                                              | None => None
                                                                              | Some (aiq_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (side_value, bytes) =>
                                                                                      match decode_uint_le 8 bytes with
                                                                                      | None => None
                                                                                      | Some (price_price_8_optional_value, bytes) =>
                                                                                          match decode_uint_le 4 bytes with
                                                                                          | None => None
                                                                                          | Some (order_qty_quantity_non_zero_value, bytes) =>
                                                                                              Some ({| account_account_optional := account_account_optional_value; instrument_id := instrument_id_value; market_participant_id_optional := market_participant_id_optional_value; cl_ord_id := cl_ord_id_value; clearing_account_optional := clearing_account_optional_value; customer_or_firm := customer_or_firm_value; open_close := open_close_value; attributed_quote_optional := attributed_quote_optional_value; time_in_force := time_in_force_value; cancel_instead_of_slide_optional := cancel_instead_of_slide_optional_value; display_inst := display_inst_value; exec_inst := exec_inst_value; ord_type := ord_type_value; target_party_id := target_party_id_value; auction_id := auction_id_value; clearing_firm := clearing_firm_value; optional_data := optional_data_value; routing_firm_id := routing_firm_id_value; aiq := aiq_value; side := side_value; price_price_8_optional := price_price_8_optional_value; order_qty_quantity_non_zero := order_qty_quantity_non_zero_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint_le by exact bound_20.
      rewrite decode_encode_uint_le by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderSingleMessage.

  Module OrderCancelReplaceRequestMessage.

    (** OrderCancelReplaceRequestMessage *)
    Record t := {
      account_account_optional : list byte;
      instrument_id : N;
      market_participant_id_optional : list byte;
      cl_ord_id : N;
      clearing_account_optional : list byte;
      orig_cl_ord_id : N;
      customer_or_firm_optional : N;
      open_close_optional : N;
      attributed_quote_optional : N;
      time_in_force_optional : N;
      cancel_instead_of_slide_optional : N;
      display_inst : N;
      exec_inst : N;
      ord_type_optional : N;
      target_party_id : list byte;
      auction_id : N;
      clearing_firm : N;
      optional_data : list byte;
      routing_firm_id : list byte;
      aiq : list byte;
      side_optional : N;
      price_price_8_optional : N;
      order_qty_quantity_non_zero : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (account_account_optional record) = 16 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id_optional record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_account_optional record) = 4 /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (customer_or_firm_optional record < 256 ^ N.of_nat 1)%N /\
      (open_close_optional record < 256 ^ N.of_nat 1)%N /\
      (attributed_quote_optional record < 256 ^ N.of_nat 1)%N /\
      (time_in_force_optional record < 256 ^ N.of_nat 1)%N /\
      (cancel_instead_of_slide_optional record < 256 ^ N.of_nat 1)%N /\
      (display_inst record < 256 ^ N.of_nat 1)%N /\
      (exec_inst record < 256 ^ N.of_nat 1)%N /\
      (ord_type_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (target_party_id record) = 4 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (clearing_firm record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (optional_data record) = 16 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (aiq record) = 3 /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      (price_price_8_optional record < 256 ^ N.of_nat 8)%N /\
      (order_qty_quantity_non_zero record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (account_account_optional record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id_optional record) ++
      encode_uint_le 8 (cl_ord_id record) ++
      encode_bytes 4 (clearing_account_optional record) ++
      encode_uint_le 8 (orig_cl_ord_id record) ++
      encode_uint 1 (customer_or_firm_optional record) ++
      encode_uint 1 (open_close_optional record) ++
      encode_uint 1 (attributed_quote_optional record) ++
      encode_uint 1 (time_in_force_optional record) ++
      encode_uint 1 (cancel_instead_of_slide_optional record) ++
      encode_uint 1 (display_inst record) ++
      encode_uint 1 (exec_inst record) ++
      encode_uint 1 (ord_type_optional record) ++
      encode_bytes 4 (target_party_id record) ++
      encode_uint_le 4 (auction_id record) ++
      encode_uint_le 4 (clearing_firm record) ++
      encode_bytes 16 (optional_data record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 3 (aiq record) ++
      encode_uint 1 (side_optional record) ++
      encode_uint_le 8 (price_price_8_optional record) ++
      encode_uint_le 4 (order_qty_quantity_non_zero record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (account_account_optional_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_optional_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (clearing_account_optional_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (orig_cl_ord_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (customer_or_firm_optional_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (open_close_optional_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (attributed_quote_optional_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (time_in_force_optional_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (cancel_instead_of_slide_optional_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (display_inst_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (exec_inst_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (ord_type_optional_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (target_party_id_value, bytes) =>
                                                                  match decode_uint_le 4 bytes with
                                                                  | None => None
                                                                  | Some (auction_id_value, bytes) =>
                                                                      match decode_uint_le 4 bytes with
                                                                      | None => None
                                                                      | Some (clearing_firm_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (optional_data_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (routing_firm_id_value, bytes) =>
                                                                                  match decode_bytes 3 bytes with
                                                                                  | None => None
                                                                                  | Some (aiq_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (side_optional_value, bytes) =>
                                                                                          match decode_uint_le 8 bytes with
                                                                                          | None => None
                                                                                          | Some (price_price_8_optional_value, bytes) =>
                                                                                              match decode_uint_le 4 bytes with
                                                                                              | None => None
                                                                                              | Some (order_qty_quantity_non_zero_value, bytes) =>
                                                                                                  Some ({| account_account_optional := account_account_optional_value; instrument_id := instrument_id_value; market_participant_id_optional := market_participant_id_optional_value; cl_ord_id := cl_ord_id_value; clearing_account_optional := clearing_account_optional_value; orig_cl_ord_id := orig_cl_ord_id_value; customer_or_firm_optional := customer_or_firm_optional_value; open_close_optional := open_close_optional_value; attributed_quote_optional := attributed_quote_optional_value; time_in_force_optional := time_in_force_optional_value; cancel_instead_of_slide_optional := cancel_instead_of_slide_optional_value; display_inst := display_inst_value; exec_inst := exec_inst_value; ord_type_optional := ord_type_optional_value; target_party_id := target_party_id_value; auction_id := auction_id_value; clearing_firm := clearing_firm_value; optional_data := optional_data_value; routing_firm_id := routing_firm_id_value; aiq := aiq_value; side_optional := side_optional_value; price_price_8_optional := price_price_8_optional_value; order_qty_quantity_non_zero := order_qty_quantity_non_zero_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint_le by exact bound_21.
      rewrite decode_encode_uint_le by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelReplaceRequestMessage.

  Module OrderCancelRequestMessage.

    (** OrderCancelRequestMessage *)
    Record t := {
      instrument_id : N;
      market_participant_id_optional : list byte;
      cl_ord_id : N;
      orig_cl_ord_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id_optional record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id_optional record) ++
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint_le 8 (orig_cl_ord_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_participant_id_optional_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      Some ({| instrument_id := instrument_id_value; market_participant_id_optional := market_participant_id_optional_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelRequestMessage.

  Module QuoteUpdatesGroupEncoding.

    (** quoteUpdatesGroupEncoding *)
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

  End QuoteUpdatesGroupEncoding.

  Module MassCancelRequestMessage.

    (** MassCancelRequestMessage *)
    Record t := {
      underlying_id_optional : N;
      market_participant_id_optional : list byte;
      cl_ord_id : N;
      send_time : N;
      ack_style_mass_cancel_ack_style : N;
      mpid_filter : N;
      bulk_action : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (underlying_id_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id_optional record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N /\
      (ack_style_mass_cancel_ack_style record < 256 ^ N.of_nat 1)%N /\
      (mpid_filter record < 256 ^ N.of_nat 1)%N /\
      (bulk_action record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (underlying_id_optional record) ++
      encode_bytes 4 (market_participant_id_optional record) ++
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint_le 8 (send_time record) ++
      encode_uint 1 (ack_style_mass_cancel_ack_style record) ++
      encode_uint 1 (mpid_filter record) ++
      encode_uint 1 (bulk_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (underlying_id_optional_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_participant_id_optional_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (send_time_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (ack_style_mass_cancel_ack_style_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (mpid_filter_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (bulk_action_value, bytes) =>
                                  Some ({| underlying_id_optional := underlying_id_optional_value; market_participant_id_optional := market_participant_id_optional_value; cl_ord_id := cl_ord_id_value; send_time := send_time_value; ack_style_mass_cancel_ack_style := ack_style_mass_cancel_ack_style_value; mpid_filter := mpid_filter_value; bulk_action := bulk_action_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelRequestMessage.

  Module CustomGroupIdsGroupEncoding.

    (** customGroupIdsGroupEncoding *)
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

  End CustomGroupIdsGroupEncoding.

  Module RiskLimitUpdateRequestMessage.

    (** RiskLimitUpdateRequestMessage *)
    Record t := {
      underlying_id_optional : N;
      market_participant_id_optional : list byte;
      cl_ord_id : N;
      risk_control_optional : N;
      risk_control_status : N;
      time_limit : N;
      percentage_limit : N;
      count_limit : N;
      ioc_attribution : N;
      cust_capacity_weight : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (underlying_id_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id_optional record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (risk_control_optional record < 256 ^ N.of_nat 1)%N /\
      (risk_control_status record < 256 ^ N.of_nat 1)%N /\
      (time_limit record < 256 ^ N.of_nat 8)%N /\
      (percentage_limit record < 256 ^ N.of_nat 4)%N /\
      (count_limit record < 256 ^ N.of_nat 4)%N /\
      (ioc_attribution record < 256 ^ N.of_nat 1)%N /\
      (cust_capacity_weight record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (underlying_id_optional record) ++
      encode_bytes 4 (market_participant_id_optional record) ++
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint 1 (risk_control_optional record) ++
      encode_uint 1 (risk_control_status record) ++
      encode_uint_le 8 (time_limit record) ++
      encode_uint_le 4 (percentage_limit record) ++
      encode_uint_le 4 (count_limit record) ++
      encode_uint 1 (ioc_attribution record) ++
      encode_uint 1 (cust_capacity_weight record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (underlying_id_optional_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_participant_id_optional_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (risk_control_optional_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (risk_control_status_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (time_limit_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (percentage_limit_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (count_limit_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (ioc_attribution_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (cust_capacity_weight_value, bytes) =>
                                              Some ({| underlying_id_optional := underlying_id_optional_value; market_participant_id_optional := market_participant_id_optional_value; cl_ord_id := cl_ord_id_value; risk_control_optional := risk_control_optional_value; risk_control_status := risk_control_status_value; time_limit := time_limit_value; percentage_limit := percentage_limit_value; count_limit := count_limit_value; ioc_attribution := ioc_attribution_value; cust_capacity_weight := cust_capacity_weight_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RiskLimitUpdateRequestMessage.

  Module RiskActionRequestMessage.

    (** RiskActionRequestMessage *)
    Record t := {
      underlying_id_optional : N;
      market_participant_id_optional : list byte;
      cl_ord_id : N;
      risk_control : N;
      risk_action : N;
      custom_group_id_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (underlying_id_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id_optional record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (risk_control record < 256 ^ N.of_nat 1)%N /\
      (risk_action record < 256 ^ N.of_nat 1)%N /\
      (custom_group_id_optional record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (underlying_id_optional record) ++
      encode_bytes 4 (market_participant_id_optional record) ++
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint 1 (risk_control record) ++
      encode_uint 1 (risk_action record) ++
      encode_uint_le 2 (custom_group_id_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (underlying_id_optional_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_participant_id_optional_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (risk_control_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (risk_action_value, bytes) =>
                          match decode_uint_le 2 bytes with
                          | None => None
                          | Some (custom_group_id_optional_value, bytes) =>
                              Some ({| underlying_id_optional := underlying_id_optional_value; market_participant_id_optional := market_participant_id_optional_value; cl_ord_id := cl_ord_id_value; risk_control := risk_control_value; risk_action := risk_action_value; custom_group_id_optional := custom_group_id_optional_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RiskActionRequestMessage.

End IexOptionsBinaryOrderEntryV103Client.
