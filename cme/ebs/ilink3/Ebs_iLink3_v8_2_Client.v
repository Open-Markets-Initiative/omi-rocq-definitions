From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * CME Group iLink 3

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
      - a field present only on a condition
      - a field read in bits
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module EbsILink3V82Client.

  Module SimpleOpenFramingHeader.

    (** Simple Open Framing Header *)
    Record t := {
      message_length : N;
      encoding_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (encoding_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (message_length record) ++
      encode_uint_le 2 (encoding_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (encoding_type_value, bytes) =>
              Some ({| message_length := message_length_value; encoding_type := encoding_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SimpleOpenFramingHeader.

  Module MessageHeader.

    (** Template ID and length of message root *)
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

  Module Sequence.

    (** The Sequence message is used in both Recoverable (CME to customer) and Idempotent (customer to CME) flows. *)
    Record t := {
      uuid : N;
      next_seq_no : N;
      fault_tolerance_indicator : N;
      keep_alive_interval_lapsed : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (next_seq_no record < 256 ^ N.of_nat 4)%N /\
      (fault_tolerance_indicator record < 256 ^ N.of_nat 1)%N /\
      (keep_alive_interval_lapsed record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (uuid record) ++
      encode_uint_le 4 (next_seq_no record) ++
      encode_uint 1 (fault_tolerance_indicator record) ++
      encode_uint 1 (keep_alive_interval_lapsed record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (uuid_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (next_seq_no_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (fault_tolerance_indicator_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (keep_alive_interval_lapsed_value, bytes) =>
                      Some ({| uuid := uuid_value; next_seq_no := next_seq_no_value; fault_tolerance_indicator := fault_tolerance_indicator_value; keep_alive_interval_lapsed := keep_alive_interval_lapsed_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Sequence.

  Module Terminate.

    (** The Terminate message is sent to indicate that the sender is going to disconnect the TCP socket connection. *)
    Record t := {
      reason : list byte;
      uuid : N;
      request_timestamp : N;
      error_codes : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 48 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (error_codes record < 256 ^ N.of_nat 2)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 48 (reason record) ++
      encode_uint_le 8 (uuid record) ++
      encode_uint_le 8 (request_timestamp record) ++
      encode_uint_le 2 (error_codes record) ++
      encode_uint 1 (split_msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 48 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (error_codes_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (split_msg_value, bytes) =>
                          Some ({| reason := reason_value; uuid := uuid_value; request_timestamp := request_timestamp_value; error_codes := error_codes_value; split_msg := split_msg_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Terminate.

  Module RetransmitRequest.

    (** Customers can send the Retransmit Request message to recover missed messages. *)
    Record t := {
      uuid : N;
      last_uuid : N;
      request_timestamp : N;
      from_seq_no : N;
      msg_count_16 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (last_uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (from_seq_no record < 256 ^ N.of_nat 4)%N /\
      (msg_count_16 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (uuid record) ++
      encode_uint_le 8 (last_uuid record) ++
      encode_uint_le 8 (request_timestamp record) ++
      encode_uint_le 4 (from_seq_no record) ++
      encode_uint_le 2 (msg_count_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (uuid_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (last_uuid_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (from_seq_no_value, bytes) =>
                      match decode_uint_le 2 bytes with
                      | None => None
                      | Some (msg_count_16_value, bytes) =>
                          Some ({| uuid := uuid_value; last_uuid := last_uuid_value; request_timestamp := request_timestamp_value; from_seq_no := from_seq_no_value; msg_count_16 := msg_count_16_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RetransmitRequest.

  Module OrderCancelRequest.

    (** Sent by client system to cancel an existing order; an order may be cancelled by referencing the Order ID. *)
    Record t := {
      order_id : N;
      party_details_list_req_id : N;
      manual_order_indicator : N;
      seq_num : N;
      sender_id : list byte;
      cl_ord_id : list byte;
      order_request_id : N;
      sending_time_epoch : N;
      location : list byte;
      security_id : N;
      side : N;
      liquidity_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (party_details_list_req_id record < 256 ^ N.of_nat 8)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (sender_id record) = 20 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (order_request_id record < 256 ^ N.of_nat 8)%N /\
      (sending_time_epoch record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (location record) = 5 /\
      (security_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (liquidity_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (party_details_list_req_id record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint_le 4 (seq_num record) ++
      encode_bytes 20 (sender_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint_le 8 (order_request_id record) ++
      encode_uint_le 8 (sending_time_epoch record) ++
      encode_bytes 5 (location record) ++
      encode_uint_le 4 (security_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (liquidity_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (party_details_list_req_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (manual_order_indicator_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (sender_id_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (cl_ord_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (order_request_id_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (sending_time_epoch_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (location_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (security_id_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (liquidity_flag_value, bytes) =>
                                                      Some ({| order_id := order_id_value; party_details_list_req_id := party_details_list_req_id_value; manual_order_indicator := manual_order_indicator_value; seq_num := seq_num_value; sender_id := sender_id_value; cl_ord_id := cl_ord_id_value; order_request_id := order_request_id_value; sending_time_epoch := sending_time_epoch_value; location := location_value; security_id := security_id_value; side := side_value; liquidity_flag := liquidity_flag_value |}, bytes)
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelRequest.

  Module GroupSize.

    (** Repeating group dimensions *)
    Record t := {
      block_length : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (block_length record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GroupSize.

  Module OrderMassStatusRequest.

    (** The Order Mass Status Request message requests the status for orders matching criteria specified within the request. *)
    Record t := {
      party_details_list_req_id : N;
      mass_status_req_id : N;
      manual_order_indicator : N;
      seq_num : N;
      sender_id : list byte;
      sending_time_epoch : N;
      security_group : list byte;
      location : list byte;
      security_id_optional : N;
      mass_status_req_type : N;
      ord_status_req_type : N;
      mass_status_tif : N;
      market_segment_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (party_details_list_req_id record < 256 ^ N.of_nat 8)%N /\
      (mass_status_req_id record < 256 ^ N.of_nat 8)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (sender_id record) = 20 /\
      (sending_time_epoch record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_group record) = 6 /\
      Datatypes.length (location record) = 5 /\
      (security_id_optional record < 256 ^ N.of_nat 4)%N /\
      (mass_status_req_type record < 256 ^ N.of_nat 1)%N /\
      (ord_status_req_type record < 256 ^ N.of_nat 1)%N /\
      (mass_status_tif record < 256 ^ N.of_nat 1)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (party_details_list_req_id record) ++
      encode_uint_le 8 (mass_status_req_id record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint_le 4 (seq_num record) ++
      encode_bytes 20 (sender_id record) ++
      encode_uint_le 8 (sending_time_epoch record) ++
      encode_bytes 6 (security_group record) ++
      encode_bytes 5 (location record) ++
      encode_uint_le 4 (security_id_optional record) ++
      encode_uint 1 (mass_status_req_type record) ++
      encode_uint 1 (ord_status_req_type record) ++
      encode_uint 1 (mass_status_tif record) ++
      encode_uint 1 (market_segment_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (party_details_list_req_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (mass_status_req_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (manual_order_indicator_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (sender_id_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (sending_time_epoch_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (security_group_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (location_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (security_id_optional_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (mass_status_req_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (ord_status_req_type_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (mass_status_tif_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (market_segment_id_value, bytes) =>
                                                          Some ({| party_details_list_req_id := party_details_list_req_id_value; mass_status_req_id := mass_status_req_id_value; manual_order_indicator := manual_order_indicator_value; seq_num := seq_num_value; sender_id := sender_id_value; sending_time_epoch := sending_time_epoch_value; security_group := security_group_value; location := location_value; security_id_optional := security_id_optional_value; mass_status_req_type := mass_status_req_type_value; ord_status_req_type := ord_status_req_type_value; mass_status_tif := mass_status_tif_value; market_segment_id := market_segment_id_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderMassStatusRequest.

  Module OrderStatusRequest.

    (** Submitted by the client system to obtain the current status of a specific order; CME Globex returns the order status in the form of an Execution Report (MsgType=8) with the status listed in tag 39-OrdStatus. *)
    Record t := {
      party_details_list_req_id : N;
      ord_status_req_id : N;
      manual_order_indicator : N;
      seq_num : N;
      sender_id : list byte;
      order_id : N;
      sending_time_epoch : N;
      location : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (party_details_list_req_id record < 256 ^ N.of_nat 8)%N /\
      (ord_status_req_id record < 256 ^ N.of_nat 8)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (sender_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (sending_time_epoch record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (location record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (party_details_list_req_id record) ++
      encode_uint_le 8 (ord_status_req_id record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint_le 4 (seq_num record) ++
      encode_bytes 20 (sender_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (sending_time_epoch record) ++
      encode_bytes 5 (location record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (party_details_list_req_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (ord_status_req_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (manual_order_indicator_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (sender_id_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (sending_time_epoch_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (location_value, bytes) =>
                                      Some ({| party_details_list_req_id := party_details_list_req_id_value; ord_status_req_id := ord_status_req_id_value; manual_order_indicator := manual_order_indicator_value; seq_num := seq_num_value; sender_id := sender_id_value; order_id := order_id_value; sending_time_epoch := sending_time_epoch_value; location := location_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderStatusRequest.

  Module ExecutionAck.

    (** The Execution Acknowledgment message notifies CME that a given fill has either been accepted or rejected by a counterparty for EU bilateral trades. *)
    Record t := {
      party_details_list_req_id : N;
      order_id : N;
      exec_ack_status : N;
      seq_num : N;
      cl_ord_id : list byte;
      sec_exec_id : N;
      last_px : N;
      security_id : N;
      last_qty : N;
      dk_reason : list byte;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (party_details_list_req_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (exec_ack_status record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (sec_exec_id record < 256 ^ N.of_nat 8)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 4)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (dk_reason record) = 1 /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (party_details_list_req_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint 1 (exec_ack_status record) ++
      encode_uint_le 4 (seq_num record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint_le 8 (sec_exec_id record) ++
      encode_uint_le 8 (last_px record) ++
      encode_uint_le 4 (security_id record) ++
      encode_uint_le 4 (last_qty record) ++
      encode_bytes 1 (dk_reason record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (party_details_list_req_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (exec_ack_status_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (sec_exec_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (last_px_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (security_id_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (dk_reason_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  Some ({| party_details_list_req_id := party_details_list_req_id_value; order_id := order_id_value; exec_ack_status := exec_ack_status_value; seq_num := seq_num_value; cl_ord_id := cl_ord_id_value; sec_exec_id := sec_exec_id_value; last_px := last_px_value; security_id := security_id_value; last_qty := last_qty_value; dk_reason := dk_reason_value; side := side_value |}, bytes)
                                              end
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionAck.

  Module LegOptionDelta.

    (** Up to 26 legs (i.e., repeating groups) supported for UDS for options. Up to 40 legs (i.e., repeating groups) supported for UDS for futures. Will be set to 0 for REPO *)
    Record t := {
      mantissa_32 : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa_32 record < 256 ^ N.of_nat 4)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (mantissa_32 record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (mantissa_32_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa_32 := mantissa_32_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End LegOptionDelta.

End EbsILink3V82Client.
