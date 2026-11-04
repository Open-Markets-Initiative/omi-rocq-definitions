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

Module IexOptionsBinaryOrderEntryV103Server.

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
      encode_uint 2 (block_length record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 2 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint 2 bytes with
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module LoginResponseMessage.

    (** LoginResponseMessage *)
    Record t := {
      logon_id : list byte;
      status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (logon_id record) = 16 /\
      (status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (logon_id record) ++
      encode_uint 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (logon_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (status_value, bytes) =>
              Some ({| logon_id := logon_id_value; status := status_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginResponseMessage.

  Module SessionInfoGroupEncoding.

    (** sessionInfoGroupEncoding *)
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

  End SessionInfoGroupEncoding.

  Module TerminateMessage.

    (** TerminateMessage *)
    Record t := {
      reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          Some ({| reason := reason_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TerminateMessage.

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
      encode_uint 8 (subsession_id record) ++
      encode_uint 4 (sequence record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (subsession_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  Some ({| subsession_id := subsession_id_value; sequence := sequence_value; timestamp := timestamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SequencedMessageHeaderMessage.

  Module SubsessionJoinResponseMessage.

    (** SubsessionJoinResponseMessage *)
    Record t := {
      subsession_id : N;
      status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (subsession_id record < 256 ^ N.of_nat 8)%N /\
      (status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (subsession_id record) ++
      encode_uint 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (subsession_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (status_value, bytes) =>
              Some ({| subsession_id := subsession_id_value; status := status_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SubsessionJoinResponseMessage.

  Module SubsessionLeaveResponseMessage.

    (** SubsessionLeaveResponseMessage *)
    Record t := {
      subsession_id : N;
      reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (subsession_id record < 256 ^ N.of_nat 8)%N /\
      (reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (subsession_id record) ++
      encode_uint 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (subsession_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (reason_value, bytes) =>
              Some ({| subsession_id := subsession_id_value; reason := reason_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SubsessionLeaveResponseMessage.

  Module OrderAckMessage.

    (** OrderAckMessage *)
    Record t := {
      account_account_optional : list byte;
      transact_time : N;
      instrument_id : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      clearing_account_optional : list byte;
      orig_cl_ord_id_optional : N;
      order_id : N;
      customer_or_firm : N;
      open_close : N;
      attributed_quote : N;
      time_in_force : N;
      cancel_instead_of_slide : N;
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
      leaves_qty : N;
      effective_limit_price : N;
      display_price : N;
      reason_code_optional : N;
      ack_type : N;
      throttle_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (account_account_optional record) = 16 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_account_optional record) = 4 /\
      (orig_cl_ord_id_optional record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (customer_or_firm record < 256 ^ N.of_nat 1)%N /\
      (open_close record < 256 ^ N.of_nat 1)%N /\
      (attributed_quote record < 256 ^ N.of_nat 1)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (cancel_instead_of_slide record < 256 ^ N.of_nat 1)%N /\
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
      (order_qty_quantity_non_zero record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (effective_limit_price record < 256 ^ N.of_nat 8)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (ack_type record < 256 ^ N.of_nat 1)%N /\
      (throttle_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (account_account_optional record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_bytes 4 (clearing_account_optional record) ++
      encode_uint 8 (orig_cl_ord_id_optional record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (customer_or_firm record) ++
      encode_uint 1 (open_close record) ++
      encode_uint 1 (attributed_quote record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (cancel_instead_of_slide record) ++
      encode_uint 1 (display_inst record) ++
      encode_uint 1 (exec_inst record) ++
      encode_uint 1 (ord_type record) ++
      encode_bytes 4 (target_party_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (clearing_firm record) ++
      encode_bytes 16 (optional_data record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 3 (aiq record) ++
      encode_uint 1 (side record) ++
      encode_uint 8 (price_price_8_optional record) ++
      encode_uint 4 (order_qty_quantity_non_zero record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (effective_limit_price record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (ack_type record) ++
      encode_uint 1 (throttle_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (account_account_optional_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_participant_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_account_optional_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (orig_cl_ord_id_optional_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (order_id_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (customer_or_firm_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (open_close_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (attributed_quote_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (time_in_force_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (cancel_instead_of_slide_value, bytes) =>
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
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (auction_id_value, bytes) =>
                                                                              match decode_uint 4 bytes with
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
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (price_price_8_optional_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (order_qty_quantity_non_zero_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (leaves_qty_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (effective_limit_price_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (display_price_value, bytes) =>
                                                                                                                      match decode_uint 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (reason_code_optional_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ack_type_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (throttle_indicator_value, bytes) =>
                                                                                                                                  Some ({| account_account_optional := account_account_optional_value; transact_time := transact_time_value; instrument_id := instrument_id_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; clearing_account_optional := clearing_account_optional_value; orig_cl_ord_id_optional := orig_cl_ord_id_optional_value; order_id := order_id_value; customer_or_firm := customer_or_firm_value; open_close := open_close_value; attributed_quote := attributed_quote_value; time_in_force := time_in_force_value; cancel_instead_of_slide := cancel_instead_of_slide_value; display_inst := display_inst_value; exec_inst := exec_inst_value; ord_type := ord_type_value; target_party_id := target_party_id_value; auction_id := auction_id_value; clearing_firm := clearing_firm_value; optional_data := optional_data_value; routing_firm_id := routing_firm_id_value; aiq := aiq_value; side := side_value; price_price_8_optional := price_price_8_optional_value; order_qty_quantity_non_zero := order_qty_quantity_non_zero_value; leaves_qty := leaves_qty_value; effective_limit_price := effective_limit_price_value; display_price := display_price_value; reason_code_optional := reason_code_optional_value; ack_type := ack_type_value; throttle_indicator := throttle_indicator_value |}, bytes)
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 139.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 bound_30]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
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
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAckMessage.

  Module UnsolicitedModifyAckMessage.

    (** UnsolicitedModifyAckMessage *)
    Record t := {
      transact_time : N;
      instrument_id : N;
      market_participant_id : list byte;
      orig_cl_ord_id : N;
      order_id : N;
      price_price_8 : N;
      order_qty_quantity_non_zero : N;
      leaves_qty : N;
      effective_limit_price : N;
      display_price : N;
      restatement_reason : N;
      reason_code_optional : N;
      ack_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price_price_8 record < 256 ^ N.of_nat 8)%N /\
      (order_qty_quantity_non_zero record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (effective_limit_price record < 256 ^ N.of_nat 8)%N /\
      (display_price record < 256 ^ N.of_nat 8)%N /\
      (restatement_reason record < 256 ^ N.of_nat 1)%N /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (ack_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (orig_cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (price_price_8 record) ++
      encode_uint 4 (order_qty_quantity_non_zero record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (effective_limit_price record) ++
      encode_uint 8 (display_price record) ++
      encode_uint 1 (restatement_reason record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (ack_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_price_8_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (order_qty_quantity_non_zero_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (leaves_qty_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (effective_limit_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (display_price_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (restatement_reason_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reason_code_optional_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (ack_type_value, bytes) =>
                                                          Some ({| transact_time := transact_time_value; instrument_id := instrument_id_value; market_participant_id := market_participant_id_value; orig_cl_ord_id := orig_cl_ord_id_value; order_id := order_id_value; price_price_8 := price_price_8_value; order_qty_quantity_non_zero := order_qty_quantity_non_zero_value; leaves_qty := leaves_qty_value; effective_limit_price := effective_limit_price_value; display_price := display_price_value; restatement_reason := restatement_reason_value; reason_code_optional := reason_code_optional_value; ack_type := ack_type_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnsolicitedModifyAckMessage.

  Module OrderCancelAckMessage.

    (** OrderCancelAckMessage *)
    Record t := {
      transact_time : N;
      instrument_id : N;
      market_participant_id : list byte;
      cl_ord_id_optional : N;
      orig_cl_ord_id : N;
      order_id_optional : N;
      price_price_8_optional : N;
      leaves_qty : N;
      reason_code_optional : N;
      ack_type : N;
      throttle_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id_optional record < 256 ^ N.of_nat 8)%N /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (price_price_8_optional record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (ack_type record < 256 ^ N.of_nat 1)%N /\
      (throttle_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id_optional record) ++
      encode_uint 8 (orig_cl_ord_id record) ++
      encode_uint 8 (order_id_optional record) ++
      encode_uint 8 (price_price_8_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (ack_type record) ++
      encode_uint 1 (throttle_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cl_ord_id_optional_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (orig_cl_ord_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_optional_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_price_8_optional_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (leaves_qty_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reason_code_optional_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (ack_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (throttle_indicator_value, bytes) =>
                                                  Some ({| transact_time := transact_time_value; instrument_id := instrument_id_value; market_participant_id := market_participant_id_value; cl_ord_id_optional := cl_ord_id_optional_value; orig_cl_ord_id := orig_cl_ord_id_value; order_id_optional := order_id_optional_value; price_price_8_optional := price_price_8_optional_value; leaves_qty := leaves_qty_value; reason_code_optional := reason_code_optional_value; ack_type := ack_type_value; throttle_indicator := throttle_indicator_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelAckMessage.

  Module MassCancelAckMessage.

    (** MassCancelAckMessage *)
    Record t := {
      transact_time : N;
      underlying_id_optional : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      reason_code_optional : N;
      ack_style_mass_cancel_ack_style : N;
      mpid_filter : N;
      bulk_action : N;
      cancel_count : N;
      throttle_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (ack_style_mass_cancel_ack_style record < 256 ^ N.of_nat 1)%N /\
      (mpid_filter record < 256 ^ N.of_nat 1)%N /\
      (bulk_action record < 256 ^ N.of_nat 1)%N /\
      (cancel_count record < 256 ^ N.of_nat 4)%N /\
      (throttle_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (underlying_id_optional record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (ack_style_mass_cancel_ack_style record) ++
      encode_uint 1 (mpid_filter record) ++
      encode_uint 1 (bulk_action record) ++
      encode_uint 4 (cancel_count record) ++
      encode_uint 1 (throttle_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_id_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reason_code_optional_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (ack_style_mass_cancel_ack_style_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (mpid_filter_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (bulk_action_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (cancel_count_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (throttle_indicator_value, bytes) =>
                                              Some ({| transact_time := transact_time_value; underlying_id_optional := underlying_id_optional_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; reason_code_optional := reason_code_optional_value; ack_style_mass_cancel_ack_style := ack_style_mass_cancel_ack_style_value; mpid_filter := mpid_filter_value; bulk_action := bulk_action_value; cancel_count := cancel_count_value; throttle_indicator := throttle_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelAckMessage.

  Module QuoteAcksGroupEncoding.

    (** quoteAcksGroupEncoding *)
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

  End QuoteAcksGroupEncoding.

  Module NewIocQuoteAckMessage.

    (** NewIocQuoteAckMessage *)
    Record t := {
      transact_time : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      clearing_account : list byte;
      aiq : list byte;
      instrument_id : N;
      side : N;
      order_id : N;
      ack_type : N;
      price_price_4_optional : N;
      order_qty_quantity_non_zero : N;
      reason_code_optional : N;
      throttle_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_account record) = 4 /\
      Datatypes.length (aiq record) = 3 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (ack_type record < 256 ^ N.of_nat 1)%N /\
      (price_price_4_optional record < 256 ^ N.of_nat 4)%N /\
      (order_qty_quantity_non_zero record < 256 ^ N.of_nat 4)%N /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (throttle_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_bytes 3 (aiq record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (ack_type record) ++
      encode_uint 4 (price_price_4_optional record) ++
      encode_uint 4 (order_qty_quantity_non_zero record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (throttle_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_participant_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (clearing_account_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (aiq_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (order_id_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (ack_type_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (price_price_4_optional_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (order_qty_quantity_non_zero_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reason_code_optional_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (throttle_indicator_value, bytes) =>
                                                          Some ({| transact_time := transact_time_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; clearing_account := clearing_account_value; aiq := aiq_value; instrument_id := instrument_id_value; side := side_value; order_id := order_id_value; ack_type := ack_type_value; price_price_4_optional := price_price_4_optional_value; order_qty_quantity_non_zero := order_qty_quantity_non_zero_value; reason_code_optional := reason_code_optional_value; throttle_indicator := throttle_indicator_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewIocQuoteAckMessage.

  Module QuoteRestatedMessage.

    (** QuoteRestatedMessage *)
    Record t := {
      transact_time : N;
      instrument_id : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      order_id : N;
      side : N;
      price_price_4 : N;
      reason_code_optional : N;
      ack_type : N;
      delta : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (price_price_4 record < 256 ^ N.of_nat 4)%N /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (ack_type record < 256 ^ N.of_nat 1)%N /\
      (delta record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (price_price_4 record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (ack_type record) ++
      encode_uint 4 (delta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_price_4_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (reason_code_optional_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (ack_type_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (delta_value, bytes) =>
                                              Some ({| transact_time := transact_time_value; instrument_id := instrument_id_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; side := side_value; price_price_4 := price_price_4_value; reason_code_optional := reason_code_optional_value; ack_type := ack_type_value; delta := delta_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRestatedMessage.

  Module QuoteCanceledMessage.

    (** QuoteCanceledMessage *)
    Record t := {
      transact_time : N;
      instrument_id : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      order_id : N;
      side : N;
      reason_code : N;
      ack_type : N;
      delta : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (reason_code record < 256 ^ N.of_nat 1)%N /\
      (ack_type record < 256 ^ N.of_nat 1)%N /\
      (delta record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (reason_code record) ++
      encode_uint 1 (ack_type record) ++
      encode_uint 4 (delta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reason_code_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (ack_type_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (delta_value, bytes) =>
                                          Some ({| transact_time := transact_time_value; instrument_id := instrument_id_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; side := side_value; reason_code := reason_code_value; ack_type := ack_type_value; delta := delta_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteCanceledMessage.

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

  Module ExecutionReportMessage.

    (** ExecutionReportMessage *)
    Record t := {
      account_account_optional : list byte;
      transact_time : N;
      instrument_id : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      clearing_account_optional : list byte;
      customer_or_firm : N;
      order_id : N;
      exec_id : N;
      trade_id : N;
      last_px : N;
      open_close : N;
      side : N;
      target_party_id : list byte;
      auction_id : N;
      clearing_firm : N;
      optional_data : list byte;
      routing_firm_id : list byte;
      aiq : list byte;
      leaves_qty : N;
      cum_qty : N;
      last_qty : N;
      trade_liquidity_indicator : N;
      fee_code : list byte;
      reason_code_optional : N;
      occ_id : list byte;
      contra_clearing_account : list byte;
      contra_clearing_firm : N;
      contra_mpid : list byte;
      contra_open_close : N;
      contra_customer_or_firm : N;
      contra_occ_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (account_account_optional record) = 16 /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (clearing_account_optional record) = 4 /\
      (customer_or_firm record < 256 ^ N.of_nat 1)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (open_close record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (target_party_id record) = 4 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (clearing_firm record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (optional_data record) = 16 /\
      Datatypes.length (routing_firm_id record) = 4 /\
      Datatypes.length (aiq record) = 3 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (trade_liquidity_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (fee_code record) = 2 /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (occ_id record) = 5 /\
      Datatypes.length (contra_clearing_account record) = 4 /\
      (contra_clearing_firm record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (contra_mpid record) = 4 /\
      (contra_open_close record < 256 ^ N.of_nat 1)%N /\
      (contra_customer_or_firm record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (contra_occ_id record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (account_account_optional record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_bytes 4 (clearing_account_optional record) ++
      encode_uint 1 (customer_or_firm record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 1 (open_close record) ++
      encode_uint 1 (side record) ++
      encode_bytes 4 (target_party_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (clearing_firm record) ++
      encode_bytes 16 (optional_data record) ++
      encode_bytes 4 (routing_firm_id record) ++
      encode_bytes 3 (aiq record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 1 (trade_liquidity_indicator record) ++
      encode_bytes 2 (fee_code record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_bytes 5 (occ_id record) ++
      encode_bytes 4 (contra_clearing_account record) ++
      encode_uint 4 (contra_clearing_firm record) ++
      encode_bytes 4 (contra_mpid record) ++
      encode_uint 1 (contra_open_close record) ++
      encode_uint 1 (contra_customer_or_firm record) ++
      encode_bytes 5 (contra_occ_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (account_account_optional_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_participant_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_account_optional_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (customer_or_firm_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (order_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (exec_id_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_id_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (last_px_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (open_close_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (target_party_id_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (auction_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
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
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (leaves_qty_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (cum_qty_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (last_qty_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (trade_liquidity_indicator_value, bytes) =>
                                                                                                  match decode_bytes 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (fee_code_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (reason_code_optional_value, bytes) =>
                                                                                                          match decode_bytes 5 bytes with
                                                                                                          | None => None
                                                                                                          | Some (occ_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (contra_clearing_account_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (contra_clearing_firm_value, bytes) =>
                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (contra_mpid_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (contra_open_close_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (contra_customer_or_firm_value, bytes) =>
                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (contra_occ_id_value, bytes) =>
                                                                                                                                      Some ({| account_account_optional := account_account_optional_value; transact_time := transact_time_value; instrument_id := instrument_id_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; clearing_account_optional := clearing_account_optional_value; customer_or_firm := customer_or_firm_value; order_id := order_id_value; exec_id := exec_id_value; trade_id := trade_id_value; last_px := last_px_value; open_close := open_close_value; side := side_value; target_party_id := target_party_id_value; auction_id := auction_id_value; clearing_firm := clearing_firm_value; optional_data := optional_data_value; routing_firm_id := routing_firm_id_value; aiq := aiq_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; last_qty := last_qty_value; trade_liquidity_indicator := trade_liquidity_indicator_value; fee_code := fee_code_value; reason_code_optional := reason_code_optional_value; occ_id := occ_id_value; contra_clearing_account := contra_clearing_account_value; contra_clearing_firm := contra_clearing_firm_value; contra_mpid := contra_mpid_value; contra_open_close := contra_open_close_value; contra_customer_or_firm := contra_customer_or_firm_value; contra_occ_id := contra_occ_id_value |}, bytes)
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 154.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 bound_31]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportMessage.

  Module TradeBustCorrectMessage.

    (** TradeBustCorrectMessage *)
    Record t := {
      transact_time : N;
      instrument_id : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      order_id : N;
      exec_id : N;
      trade_id_optional : N;
      trade_ref_id : N;
      last_px : N;
      account_account_optional : list byte;
      last_qty : N;
      reason_code_optional : N;
      bust_or_correction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id_optional record < 256 ^ N.of_nat 8)%N /\
      (trade_ref_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_account_optional record) = 16 /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (bust_or_correction record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (trade_id_optional record) ++
      encode_uint 8 (trade_ref_id record) ++
      encode_uint 8 (last_px record) ++
      encode_bytes 16 (account_account_optional record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (bust_or_correction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (exec_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_id_optional_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_ref_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_px_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (account_account_optional_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (last_qty_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reason_code_optional_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (bust_or_correction_value, bytes) =>
                                                          Some ({| transact_time := transact_time_value; instrument_id := instrument_id_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; order_id := order_id_value; exec_id := exec_id_value; trade_id_optional := trade_id_optional_value; trade_ref_id := trade_ref_id_value; last_px := last_px_value; account_account_optional := account_account_optional_value; last_qty := last_qty_value; reason_code_optional := reason_code_optional_value; bust_or_correction := bust_or_correction_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeBustCorrectMessage.

  Module ApplicationLayerRejectMessage.

    (** ApplicationLayerRejectMessage *)
    Record t := {
      transact_time : N;
      underlying_id_optional : N;
      instrument_id_instrument_id_optional : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      account_string_16_optional : list byte;
      reason_code_optional : N;
      reject_type : N;
      throttle_indicator_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id_optional record < 256 ^ N.of_nat 4)%N /\
      (instrument_id_instrument_id_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account_string_16_optional record) = 16 /\
      (reason_code_optional record < 256 ^ N.of_nat 1)%N /\
      (reject_type record < 256 ^ N.of_nat 1)%N /\
      (throttle_indicator_optional record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (underlying_id_optional record) ++
      encode_uint 4 (instrument_id_instrument_id_optional record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_bytes 16 (account_string_16_optional record) ++
      encode_uint 1 (reason_code_optional record) ++
      encode_uint 1 (reject_type record) ++
      encode_uint 1 (throttle_indicator_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_id_optional_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_instrument_id_optional_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_participant_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (account_string_16_optional_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reason_code_optional_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (reject_type_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (throttle_indicator_optional_value, bytes) =>
                                          Some ({| transact_time := transact_time_value; underlying_id_optional := underlying_id_optional_value; instrument_id_instrument_id_optional := instrument_id_instrument_id_optional_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; account_string_16_optional := account_string_16_optional_value; reason_code_optional := reason_code_optional_value; reject_type := reject_type_value; throttle_indicator_optional := throttle_indicator_optional_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ApplicationLayerRejectMessage.

  Module UnderlyingRefDataMessage.

    (** UnderlyingRefDataMessage *)
    Record t := {
      transact_time : N;
      underlying_id : N;
      underlying_symbol : list byte;
      mic : list byte;
      mpv_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 8 /\
      Datatypes.length (mic record) = 4 /\
      (mpv_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (underlying_id record) ++
      encode_bytes 8 (underlying_symbol record) ++
      encode_bytes 4 (mic record) ++
      encode_uint 1 (mpv_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (mic_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (mpv_group_value, bytes) =>
                          Some ({| transact_time := transact_time_value; underlying_id := underlying_id_value; underlying_symbol := underlying_symbol_value; mic := mic_value; mpv_group := mpv_group_value |}, bytes)
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingRefDataMessage.

  Module InstrumentRefDataMessage.

    (** InstrumentRefDataMessage *)
    Record t := {
      transact_time : N;
      instrument_id : N;
      underlying_id : N;
      osi_symbol : list byte;
      maturity_date : list byte;
      option_type : N;
      strike_price : N;
      closing_only : N;
      orp_enabled : N;
      trading_ring : N;
      matching_unit : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (underlying_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (osi_symbol record) = 21 /\
      Datatypes.length (maturity_date record) = 8 /\
      (option_type record < 256 ^ N.of_nat 1)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (closing_only record < 256 ^ N.of_nat 1)%N /\
      (orp_enabled record < 256 ^ N.of_nat 1)%N /\
      (trading_ring record < 256 ^ N.of_nat 1)%N /\
      (matching_unit record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (underlying_id record) ++
      encode_bytes 21 (osi_symbol record) ++
      encode_bytes 8 (maturity_date record) ++
      encode_uint 1 (option_type record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 1 (closing_only record) ++
      encode_uint 1 (orp_enabled record) ++
      encode_uint 1 (trading_ring record) ++
      encode_uint 2 (matching_unit record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (underlying_id_value, bytes) =>
                  match decode_bytes 21 bytes with
                  | None => None
                  | Some (osi_symbol_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (maturity_date_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (option_type_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (strike_price_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (closing_only_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (orp_enabled_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trading_ring_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (matching_unit_value, bytes) =>
                                                  Some ({| transact_time := transact_time_value; instrument_id := instrument_id_value; underlying_id := underlying_id_value; osi_symbol := osi_symbol_value; maturity_date := maturity_date_value; option_type := option_type_value; strike_price := strike_price_value; closing_only := closing_only_value; orp_enabled := orp_enabled_value; trading_ring := trading_ring_value; matching_unit := matching_unit_value |}, bytes)
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentRefDataMessage.

  Module MpidConfigurationAcknowledgementMessage.

    (** MPIDConfigurationAcknowledgementMessage *)
    Record t := {
      transact_time : N;
      market_participant_id : list byte;
      mpid_status : N;
      member : list byte;
      max_qty : N;
      max_notional : N;
      default_account : list byte;
      default_optional_data : list byte;
      default_clearing_account : list byte;
      allow_market_orders : N;
      allow_isoioc : N;
      allow_iso_day : N;
      max_duplicative : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (mpid_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (member record) = 8 /\
      (max_qty record < 256 ^ N.of_nat 4)%N /\
      (max_notional record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (default_account record) = 16 /\
      Datatypes.length (default_optional_data record) = 16 /\
      Datatypes.length (default_clearing_account record) = 4 /\
      (allow_market_orders record < 256 ^ N.of_nat 1)%N /\
      (allow_isoioc record < 256 ^ N.of_nat 1)%N /\
      (allow_iso_day record < 256 ^ N.of_nat 1)%N /\
      (max_duplicative record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 1 (mpid_status record) ++
      encode_bytes 8 (member record) ++
      encode_uint 4 (max_qty record) ++
      encode_uint 8 (max_notional record) ++
      encode_bytes 16 (default_account record) ++
      encode_bytes 16 (default_optional_data record) ++
      encode_bytes 4 (default_clearing_account record) ++
      encode_uint 1 (allow_market_orders record) ++
      encode_uint 1 (allow_isoioc record) ++
      encode_uint 1 (allow_iso_day record) ++
      encode_uint 4 (max_duplicative record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_participant_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (mpid_status_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (member_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_qty_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (max_notional_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (default_account_value, bytes) =>
                                  match decode_bytes 16 bytes with
                                  | None => None
                                  | Some (default_optional_data_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (default_clearing_account_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (allow_market_orders_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (allow_isoioc_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (allow_iso_day_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (max_duplicative_value, bytes) =>
                                                          Some ({| transact_time := transact_time_value; market_participant_id := market_participant_id_value; mpid_status := mpid_status_value; member := member_value; max_qty := max_qty_value; max_notional := max_notional_value; default_account := default_account_value; default_optional_data := default_optional_data_value; default_clearing_account := default_clearing_account_value; allow_market_orders := allow_market_orders_value; allow_isoioc := allow_isoioc_value; allow_iso_day := allow_iso_day_value; max_duplicative := max_duplicative_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MpidConfigurationAcknowledgementMessage.

  Module MarketMakerSymbolAppointmentMessage.

    (** MarketMakerSymbolAppointmentMessage *)
    Record t := {
      transact_time : N;
      underlying_id : N;
      market_participant_id : list byte;
      appointment_type : N;
      appointment_status : N;
      max_allowable_width : N;
      quote_relief_mult : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (appointment_type record < 256 ^ N.of_nat 1)%N /\
      (appointment_status record < 256 ^ N.of_nat 1)%N /\
      (max_allowable_width record < 256 ^ N.of_nat 4)%N /\
      (quote_relief_mult record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (underlying_id record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 1 (appointment_type record) ++
      encode_uint 1 (appointment_status record) ++
      encode_uint 4 (max_allowable_width record) ++
      encode_uint 4 (quote_relief_mult record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (appointment_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (appointment_status_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (max_allowable_width_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quote_relief_mult_value, bytes) =>
                                  Some ({| transact_time := transact_time_value; underlying_id := underlying_id_value; market_participant_id := market_participant_id_value; appointment_type := appointment_type_value; appointment_status := appointment_status_value; max_allowable_width := max_allowable_width_value; quote_relief_mult := quote_relief_mult_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketMakerSymbolAppointmentMessage.

  Module SessionConfigurationAcknowledgementMessage.

    (** SessionConfigurationAcknowledgementMessage *)
    Record t := {
      transact_time : N;
      user_session_type : N;
      user_session_status : N;
      member : list byte;
      default_mpid : list byte;
      mic : list byte;
      cancel_on_disconnect : N;
      aiq_default : list byte;
      order_unsolicited_ack_subscription : N;
      quote_unsolicited_ack_subscription : N;
      default_attributed_quote : N;
      default_cancel_instead_of_slide : N;
      trading_ring_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (user_session_type record < 256 ^ N.of_nat 1)%N /\
      (user_session_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (member record) = 8 /\
      Datatypes.length (default_mpid record) = 4 /\
      Datatypes.length (mic record) = 4 /\
      (cancel_on_disconnect record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (aiq_default record) = 3 /\
      (order_unsolicited_ack_subscription record < 256 ^ N.of_nat 1)%N /\
      (quote_unsolicited_ack_subscription record < 256 ^ N.of_nat 1)%N /\
      (default_attributed_quote record < 256 ^ N.of_nat 1)%N /\
      (default_cancel_instead_of_slide record < 256 ^ N.of_nat 1)%N /\
      (trading_ring_optional record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 1 (user_session_type record) ++
      encode_uint 1 (user_session_status record) ++
      encode_bytes 8 (member record) ++
      encode_bytes 4 (default_mpid record) ++
      encode_bytes 4 (mic record) ++
      encode_uint 1 (cancel_on_disconnect record) ++
      encode_bytes 3 (aiq_default record) ++
      encode_uint 1 (order_unsolicited_ack_subscription record) ++
      encode_uint 1 (quote_unsolicited_ack_subscription record) ++
      encode_uint 1 (default_attributed_quote record) ++
      encode_uint 1 (default_cancel_instead_of_slide record) ++
      encode_uint 1 (trading_ring_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (user_session_type_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (user_session_status_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (member_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (default_mpid_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (mic_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (cancel_on_disconnect_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (aiq_default_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_unsolicited_ack_subscription_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (quote_unsolicited_ack_subscription_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (default_attributed_quote_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (default_cancel_instead_of_slide_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (trading_ring_optional_value, bytes) =>
                                                          Some ({| transact_time := transact_time_value; user_session_type := user_session_type_value; user_session_status := user_session_status_value; member := member_value; default_mpid := default_mpid_value; mic := mic_value; cancel_on_disconnect := cancel_on_disconnect_value; aiq_default := aiq_default_value; order_unsolicited_ack_subscription := order_unsolicited_ack_subscription_value; quote_unsolicited_ack_subscription := quote_unsolicited_ack_subscription_value; default_attributed_quote := default_attributed_quote_value; default_cancel_instead_of_slide := default_cancel_instead_of_slide_value; trading_ring_optional := trading_ring_optional_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SessionConfigurationAcknowledgementMessage.

  Module RiskControlAcknowledgmentMessage.

    (** RiskControlAcknowledgmentMessage *)
    Record t := {
      transact_time : N;
      underlying_id_optional : N;
      market_participant_id : list byte;
      cl_ord_id : N;
      custom_group_id_optional : N;
      risk_ack_type : N;
      risk_control_status : N;
      risk_control : N;
      risk_action_optional : N;
      time_limit : N;
      percentage_limit : N;
      count_limit : N;
      ioc_attribution : N;
      blocked_by_breach_indicator : N;
      cust_capacity_weight : N;
      throttle_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (custom_group_id_optional record < 256 ^ N.of_nat 2)%N /\
      (risk_ack_type record < 256 ^ N.of_nat 1)%N /\
      (risk_control_status record < 256 ^ N.of_nat 1)%N /\
      (risk_control record < 256 ^ N.of_nat 1)%N /\
      (risk_action_optional record < 256 ^ N.of_nat 1)%N /\
      (time_limit record < 256 ^ N.of_nat 8)%N /\
      (percentage_limit record < 256 ^ N.of_nat 4)%N /\
      (count_limit record < 256 ^ N.of_nat 4)%N /\
      (ioc_attribution record < 256 ^ N.of_nat 1)%N /\
      (blocked_by_breach_indicator record < 256 ^ N.of_nat 1)%N /\
      (cust_capacity_weight record < 256 ^ N.of_nat 1)%N /\
      (throttle_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (underlying_id_optional record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 2 (custom_group_id_optional record) ++
      encode_uint 1 (risk_ack_type record) ++
      encode_uint 1 (risk_control_status record) ++
      encode_uint 1 (risk_control record) ++
      encode_uint 1 (risk_action_optional record) ++
      encode_uint 8 (time_limit record) ++
      encode_uint 4 (percentage_limit record) ++
      encode_uint 4 (count_limit record) ++
      encode_uint 1 (ioc_attribution record) ++
      encode_uint 1 (blocked_by_breach_indicator record) ++
      encode_uint 1 (cust_capacity_weight record) ++
      encode_uint 1 (throttle_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_id_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (custom_group_id_optional_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (risk_ack_type_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (risk_control_status_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (risk_control_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (risk_action_optional_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (time_limit_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (percentage_limit_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (count_limit_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (ioc_attribution_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (blocked_by_breach_indicator_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (cust_capacity_weight_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (throttle_indicator_value, bytes) =>
                                                                      Some ({| transact_time := transact_time_value; underlying_id_optional := underlying_id_optional_value; market_participant_id := market_participant_id_value; cl_ord_id := cl_ord_id_value; custom_group_id_optional := custom_group_id_optional_value; risk_ack_type := risk_ack_type_value; risk_control_status := risk_control_status_value; risk_control := risk_control_value; risk_action_optional := risk_action_optional_value; time_limit := time_limit_value; percentage_limit := percentage_limit_value; count_limit := count_limit_value; ioc_attribution := ioc_attribution_value; blocked_by_breach_indicator := blocked_by_breach_indicator_value; cust_capacity_weight := cust_capacity_weight_value; throttle_indicator := throttle_indicator_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RiskControlAcknowledgmentMessage.

  Module RiskControlAlertMessage.

    (** RiskControlAlertMessage *)
    Record t := {
      transact_time : N;
      underlying_id_optional : N;
      market_participant_id : list byte;
      risk_control : N;
      time_limit : N;
      percentage_limit : N;
      count_limit : N;
      notification_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_participant_id record) = 4 /\
      (risk_control record < 256 ^ N.of_nat 1)%N /\
      (time_limit record < 256 ^ N.of_nat 8)%N /\
      (percentage_limit record < 256 ^ N.of_nat 4)%N /\
      (count_limit record < 256 ^ N.of_nat 4)%N /\
      (notification_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (underlying_id_optional record) ++
      encode_bytes 4 (market_participant_id record) ++
      encode_uint 1 (risk_control record) ++
      encode_uint 8 (time_limit record) ++
      encode_uint 4 (percentage_limit record) ++
      encode_uint 4 (count_limit record) ++
      encode_uint 1 (notification_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_id_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_participant_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (risk_control_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (time_limit_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (percentage_limit_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (count_limit_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (notification_reason_value, bytes) =>
                                      Some ({| transact_time := transact_time_value; underlying_id_optional := underlying_id_optional_value; market_participant_id := market_participant_id_value; risk_control := risk_control_value; time_limit := time_limit_value; percentage_limit := percentage_limit_value; count_limit := count_limit_value; notification_reason := notification_reason_value |}, bytes)
                                  end
                              end
                          end
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RiskControlAlertMessage.

End IexOptionsBinaryOrderEntryV103Server.
