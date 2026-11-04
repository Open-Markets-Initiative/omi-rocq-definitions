From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Members Exchange Members Orders

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
      - the dispatch that chooses a message by its type
      - a field read in bits
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module MemxOptionsMemoV110Server.

  Module CommonHeader.

    (** Tcp Common Header *)
    Record t := {
      message_type : N;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_type record < 256 ^ N.of_nat 1)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_type record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_length_value, bytes) =>
              Some ({| message_type := message_type_value; message_length := message_length_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End CommonHeader.

  Module LoginAcceptedMessage.

    (** Memx Tcp Login Accepted Message *)
    Record t := {
      supported_request_mode : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (supported_request_mode record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (supported_request_mode record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (supported_request_mode_value, bytes) =>
          Some ({| supported_request_mode := supported_request_mode_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginAcceptedMessage.

  Module LoginRejectedMessage.

    (** Memx Tcp Login Rejected Message *)
    Record t := {
      login_reject_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_reject_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_reject_code_value, bytes) =>
          Some ({| login_reject_code := login_reject_code_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRejectedMessage.

  Module StartOfSessionMessage.

    (** Memx Tcp Start of Session Message *)
    Record t := {
      session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          Some ({| session_id := session_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End StartOfSessionMessage.

  Module ReplayBeginMessage.

    (** Memx Tcp Replay Begin Message *)
    Record t := {
      next_sequence_number : N;
      pending_message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (pending_message_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (next_sequence_number record) ++
      encode_uint 4 (pending_message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (next_sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (pending_message_count_value, bytes) =>
              Some ({| next_sequence_number := next_sequence_number_value; pending_message_count := pending_message_count_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ReplayBeginMessage.

  Module ReplayRejectedMessage.

    (** Memx Tcp Replay Rejected Message *)
    Record t := {
      replay_reject_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (replay_reject_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (replay_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (replay_reject_code_value, bytes) =>
          Some ({| replay_reject_code := replay_reject_code_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplayRejectedMessage.

  Module ReplayCompleteMessage.

    (** Memx Tcp Replay Complete Message *)
    Record t := {
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_count record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (message_count_value, bytes) =>
          Some ({| message_count := message_count_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End ReplayCompleteMessage.

  Module StreamBeginMessage.

    (** Memx Tcp Stream Begin Message *)
    Record t := {
      next_sequence_number : N;
      max_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (max_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (next_sequence_number record) ++
      encode_uint 8 (max_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (next_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (max_sequence_number_value, bytes) =>
              Some ({| next_sequence_number := next_sequence_number_value; max_sequence_number := max_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End StreamBeginMessage.

  Module StreamRejectedMessage.

    (** Memx Tcp Stream Rejected Message *)
    Record t := {
      stream_reject_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stream_reject_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (stream_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (stream_reject_code_value, bytes) =>
          Some ({| stream_reject_code := stream_reject_code_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StreamRejectedMessage.

  Module StreamCompleteMessage.

    (** Memx Tcp Stream Complete Message *)
    Record t := {
      total_sequence_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (total_sequence_count record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (total_sequence_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (total_sequence_count_value, bytes) =>
          Some ({| total_sequence_count := total_sequence_count_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End StreamCompleteMessage.

  Module SbeHeader.

    (** Sbe Header *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
      num_groups : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 1)%N /\
      (schema_id record < 256 ^ N.of_nat 1)%N /\
      (version record < 256 ^ N.of_nat 2)%N /\
      (num_groups record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (template_id record) ++
      encode_uint 1 (schema_id record) ++
      encode_uint 2 (version record) ++
      encode_uint 1 (num_groups record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (num_groups_value, bytes) =>
                          Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value; num_groups := num_groups_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SbeHeader.

  Module RepeatingGroupDimensions.

    (** RepeatingGroupDimensions *)
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

  End RepeatingGroupDimensions.

  Module ExecutionReportBulkQuoteComponentNewMessage.

    (** ExecutionReport_BulkQuote_ComponentNewMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      exec_id : N;
      ord_status : list byte;
      security_id : list byte;
      side : list byte;
      order_qty : N;
      price_optional : N;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 8 (price_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (ord_status_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_qty_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_optional_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (cum_qty_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (sending_time_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (transact_time_value, bytes) =>
                                                          Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; exec_id := exec_id_value; ord_status := ord_status_value; security_id := security_id_value; side := side_value; order_qty := order_qty_value; price_optional := price_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value; transact_time := transact_time_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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

  End ExecutionReportBulkQuoteComponentNewMessage.

  Module ExecutionReportRejectedMessage.

    (** ExecutionReport_RejectedMessage *)
    Record t := {
      cl_ord_id : list byte;
      list_seq_no : N;
      exec_id : N;
      ord_status : list byte;
      order_reject_reason : N;
      security_id : list byte;
      side : list byte;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      (order_reject_reason record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 2 (order_reject_reason record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (list_seq_no_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exec_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (ord_status_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (order_reject_reason_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (leaves_qty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (cum_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (sending_time_value, bytes) =>
                                              Some ({| cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; exec_id := exec_id_value; ord_status := ord_status_value; order_reject_reason := order_reject_reason_value; security_id := security_id_value; side := side_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportRejectedMessage.

  Module ExecutionReportPendingCancelMessage.

    (** ExecutionReport_PendingCancelMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      orig_cl_ord_id : list byte;
      ord_status : list byte;
      security_id : list byte;
      side_optional : list byte;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side_optional record) = 1 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (ord_status_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_optional_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (leaves_qty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (cum_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (sending_time_value, bytes) =>
                                              Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; orig_cl_ord_id := orig_cl_ord_id_value; ord_status := ord_status_value; security_id := security_id_value; side_optional := side_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 75.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportPendingCancelMessage.

  Module ExecutionReportCanceledMessage.

    (** ExecutionReport_CanceledMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      orig_cl_ord_id_optional : list byte;
      exec_id : N;
      ord_status : list byte;
      cancel_reason : N;
      security_id : list byte;
      side_optional : list byte;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
      transact_time : N;
      orig_list_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (orig_cl_ord_id_optional record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      (cancel_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side_optional record) = 1 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (orig_list_seq_no record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_bytes 20 (orig_cl_ord_id_optional record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_uint 1 (cancel_reason record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 1 (orig_list_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_optional_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (ord_status_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (cancel_reason_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (security_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_optional_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (cum_qty_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (sending_time_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (transact_time_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (orig_list_seq_no_value, bytes) =>
                                                              Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; orig_cl_ord_id_optional := orig_cl_ord_id_optional_value; exec_id := exec_id_value; ord_status := ord_status_value; cancel_reason := cancel_reason_value; security_id := security_id_value; side_optional := side_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value; transact_time := transact_time_value; orig_list_seq_no := orig_list_seq_no_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportCanceledMessage.

  Module ExecutionReportPendingReplaceMessage.

    (** ExecutionReport_PendingReplaceMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      orig_cl_ord_id : list byte;
      exec_id : N;
      ord_status : list byte;
      security_id : list byte;
      side : list byte;
      order_qty : N;
      ord_type : list byte;
      price_optional : N;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (ord_status_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (security_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (order_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_optional_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (leaves_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (cum_qty_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (sending_time_value, bytes) =>
                                                              Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; ord_status := ord_status_value; security_id := security_id_value; side := side_value; order_qty := order_qty_value; ord_type := ord_type_value; price_optional := price_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 96.
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
      rewrite decode_encode_uint by exact bound_2.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportPendingReplaceMessage.

  Module ExecutionReportReplacedMessage.

    (** ExecutionReport_ReplacedMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      orig_cl_ord_id : list byte;
      exec_id : N;
      ord_status : list byte;
      security_id : list byte;
      side : list byte;
      order_qty : N;
      ord_type : list byte;
      price_optional : N;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
      transact_time : N;
      orig_list_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (orig_cl_ord_id record) = 20 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_type record) = 1 /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (orig_list_seq_no record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_bytes 20 (orig_cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_type record) ++
      encode_uint 8 (price_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 1 (orig_list_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (ord_status_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (security_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (order_qty_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_optional_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (leaves_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (cum_qty_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (sending_time_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (transact_time_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (orig_list_seq_no_value, bytes) =>
                                                                      Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; ord_status := ord_status_value; security_id := security_id_value; side := side_value; order_qty := order_qty_value; ord_type := ord_type_value; price_optional := price_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value; transact_time := transact_time_value; orig_list_seq_no := orig_list_seq_no_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportReplacedMessage.

  Module ExecutionReportTradeCorrectionMessage.

    (** ExecutionReport_TradeCorrectionMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      trd_match_id : N;
      exec_id : N;
      exec_ref_id : N;
      ord_status : list byte;
      security_id : list byte;
      side : list byte;
      last_qty : N;
      last_px : N;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      (trd_match_id record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_uint 8 (trd_match_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trd_match_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (exec_ref_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_status_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (security_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (last_qty_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (last_px_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (leaves_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (cum_qty_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (sending_time_value, bytes) =>
                                                              Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; trd_match_id := trd_match_id_value; exec_id := exec_id_value; exec_ref_id := exec_ref_id_value; ord_status := ord_status_value; security_id := security_id_value; side := side_value; last_qty := last_qty_value; last_px := last_px_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportTradeCorrectionMessage.

  Module ExecutionReportTradeBreakMessage.

    (** ExecutionReport_TradeBreakMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      trd_match_id : N;
      exec_id : N;
      exec_ref_id : N;
      ord_status : list byte;
      security_id : list byte;
      side : list byte;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      (trd_match_id record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (security_id record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_uint 8 (trd_match_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 8 (security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trd_match_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (exec_ref_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ord_status_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (security_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (leaves_qty_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (cum_qty_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (sending_time_value, bytes) =>
                                                      Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; trd_match_id := trd_match_id_value; exec_id := exec_id_value; exec_ref_id := exec_ref_id_value; ord_status := ord_status_value; security_id := security_id_value; side := side_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportTradeBreakMessage.

  Module ExecutionReportRestatementMessage.

    (** ExecutionReport_RestatementMessage *)
    Record t := {
      order_id : N;
      cl_ord_id : list byte;
      list_seq_no : N;
      exec_id : N;
      ord_status : list byte;
      security_id : list byte;
      exec_restatement_reason : N;
      extended_restatement_reason : N;
      side : list byte;
      last_px : N;
      last_qty_optional : N;
      leaves_qty : N;
      cum_qty : N;
      sending_time : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (security_id record) = 8 /\
      (exec_restatement_reason record < 256 ^ N.of_nat 1)%N /\
      (extended_restatement_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty_optional record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 8 (security_id record) ++
      encode_uint 1 (exec_restatement_reason record) ++
      encode_uint 1 (extended_restatement_reason record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (list_seq_no_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (ord_status_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (security_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (exec_restatement_reason_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (extended_restatement_reason_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (last_px_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (last_qty_optional_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (leaves_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (cum_qty_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (sending_time_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (transact_time_value, bytes) =>
                                                                  Some ({| order_id := order_id_value; cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; exec_id := exec_id_value; ord_status := ord_status_value; security_id := security_id_value; exec_restatement_reason := exec_restatement_reason_value; extended_restatement_reason := extended_restatement_reason_value; side := side_value; last_px := last_px_value; last_qty_optional := last_qty_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; sending_time := sending_time_value; transact_time := transact_time_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 85.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportRestatementMessage.

  Module MassCancelDoneMessage.

    (** MassCancelDoneMessage *)
    Record t := {
      cl_ord_id : list byte;
      total_affected_orders : N;
      sending_time : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (total_affected_orders record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 4 (total_affected_orders record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (total_affected_orders_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transact_time_value, bytes) =>
                      Some ({| cl_ord_id := cl_ord_id_value; total_affected_orders := total_affected_orders_value; sending_time := sending_time_value; transact_time := transact_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelDoneMessage.

  Module OrderCancelRejectMessage.

    (** OrderCancelRejectMessage *)
    Record t := {
      cl_ord_id : list byte;
      list_seq_no : N;
      cxl_rej_response_to : list byte;
      cxl_rej_reason : N;
      options_security_id_optional : list byte;
      side_optional : list byte;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (list_seq_no record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (cxl_rej_response_to record) = 1 /\
      (cxl_rej_reason record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (options_security_id_optional record) = 8 /\
      Datatypes.length (side_optional record) = 1 /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (list_seq_no record) ++
      encode_bytes 1 (cxl_rej_response_to record) ++
      encode_uint 2 (cxl_rej_reason record) ++
      encode_bytes 8 (options_security_id_optional record) ++
      encode_bytes 1 (side_optional record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (list_seq_no_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (cxl_rej_response_to_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (cxl_rej_reason_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (options_security_id_optional_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_optional_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (sending_time_value, bytes) =>
                                  Some ({| cl_ord_id := cl_ord_id_value; list_seq_no := list_seq_no_value; cxl_rej_response_to := cxl_rej_response_to_value; cxl_rej_reason := cxl_rej_reason_value; options_security_id_optional := options_security_id_optional_value; side_optional := side_optional_value; sending_time := sending_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelRejectMessage.

  Module UserNotificationMessage.

    (** UserNotificationMessage *)
    Record t := {
      sending_time : N;
      user_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (user_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (user_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (user_status_value, bytes) =>
              Some ({| sending_time := sending_time_value; user_status := user_status_value |}, bytes)
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

  End UserNotificationMessage.

  Module MassCancelClearLockoutRejectMessage.

    (** MassCancelClearLockoutRejectMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier : list byte;
      lockout_id : N;
      rej_reason : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier record) = 6 /\
      (lockout_id record < 256 ^ N.of_nat 8)%N /\
      (rej_reason record < 256 ^ N.of_nat 2)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier record) ++
      encode_uint 8 (lockout_id record) ++
      encode_uint 2 (rej_reason record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (lockout_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (rej_reason_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sending_time_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier := underlier_value; lockout_id := lockout_id_value; rej_reason := rej_reason_value; sending_time := sending_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelClearLockoutRejectMessage.

  Module MassCancelClearLockoutDoneMessage.

    (** MassCancelClearLockoutDoneMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier : list byte;
      lockout_id : N;
      sending_time : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier record) = 6 /\
      (lockout_id record < 256 ^ N.of_nat 8)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier record) ++
      encode_uint 8 (lockout_id record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (lockout_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (sending_time_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transact_time_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier := underlier_value; lockout_id := lockout_id_value; sending_time := sending_time_value; transact_time := transact_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelClearLockoutDoneMessage.

  Module MassCancelBulkClearLockoutRejectMessage.

    (** MassCancelBulkClearLockoutRejectMessage *)
    Record t := {
      cl_ord_id : list byte;
      rej_reason : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (rej_reason record < 256 ^ N.of_nat 2)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (rej_reason record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (rej_reason_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  Some ({| cl_ord_id := cl_ord_id_value; rej_reason := rej_reason_value; sending_time := sending_time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelBulkClearLockoutRejectMessage.

  Module MassCancelBulkClearLockoutAcceptedMessage.

    (** MassCancelBulkClearLockoutAcceptedMessage *)
    Record t := {
      cl_ord_id : list byte;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              Some ({| cl_ord_id := cl_ord_id_value; sending_time := sending_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End MassCancelBulkClearLockoutAcceptedMessage.

End MemxOptionsMemoV110Server.
