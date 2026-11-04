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

    License: MIT No Attribution
  *)

Module MemxEquitiesMemoV11Server.

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
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 1)%N /\
      (schema_id record < 256 ^ N.of_nat 1)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (template_id record) ++
      encode_uint 1 (schema_id record) ++
      encode_uint 2 (version record).

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
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End SbeHeader.

  Module ExecutionReportRejectedMessage.

    (** ExecutionReport_RejectedMessage *)
    Record t := {
      sending_time : N;
      cl_ord_id : list byte;
      exec_id : N;
      ord_status : N;
      symbol : list byte;
      symbol_sfx : list byte;
      leaves_qty : N;
      cum_qty : N;
      order_reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (order_reject_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 1 (ord_status record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 1 (order_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exec_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (ord_status_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (symbol_sfx_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cum_qty_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_reject_reason_value, bytes) =>
                                          Some ({| sending_time := sending_time_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; ord_status := ord_status_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; order_reject_reason := order_reject_reason_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportRejectedMessage.

  Module ExecutionReportTradeMessage.

    (** ExecutionReport_TradeMessage *)
    Record t := {
      sending_time : N;
      order_id : N;
      cl_ord_id : list byte;
      exec_id : N;
      ord_status : N;
      last_qty : N;
      last_px : N;
      leaves_qty : N;
      cum_qty : N;
      transact_time : N;
      last_liquidity_ind : N;
      last_mkt : list byte;
      trd_matching_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (last_liquidity_ind record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (last_mkt record) = 1 /\
      (trd_matching_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 1 (last_liquidity_ind record) ++
      encode_bytes 1 (last_mkt record) ++
      encode_uint 8 (trd_matching_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (ord_status_value, bytes) =>
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
                                          | Some (transact_time_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (last_liquidity_ind_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (last_mkt_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (trd_matching_id_value, bytes) =>
                                                          Some ({| sending_time := sending_time_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; ord_status := ord_status_value; last_qty := last_qty_value; last_px := last_px_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; transact_time := transact_time_value; last_liquidity_ind := last_liquidity_ind_value; last_mkt := last_mkt_value; trd_matching_id := trd_matching_id_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportTradeMessage.

  Module ExecutionReportPendingCancelMessage.

    (** ExecutionReport_PendingCancelMessage *)
    Record t := {
      sending_time : N;
      order_id : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : N;
      symbol : list byte;
      symbol_sfx : list byte;
      ord_status : N;
      leaves_qty : N;
      cum_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (symbol_sfx_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (ord_status_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (leaves_qty_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (cum_qty_value, bytes) =>
                                              Some ({| sending_time := sending_time_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; ord_status := ord_status_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value |}, bytes)
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

  End ExecutionReportPendingCancelMessage.

  Module PendingMassCancelMessage.

    (** PendingMassCancelMessage *)
    Record t := {
      sending_time : N;
      cl_ord_id : list byte;
      symbol : list byte;
      symbol_sfx : list byte;
      side : N;
      lower_than_price : N;
      higher_than_price : N;
      cancel_group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (lower_than_price record < 256 ^ N.of_nat 8)%N /\
      (higher_than_price record < 256 ^ N.of_nat 8)%N /\
      (cancel_group_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_uint 1 (side record) ++
      encode_uint 8 (lower_than_price record) ++
      encode_uint 8 (higher_than_price record) ++
      encode_uint 2 (cancel_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (symbol_sfx_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (lower_than_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (higher_than_price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (cancel_group_id_value, bytes) =>
                                      Some ({| sending_time := sending_time_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; side := side_value; lower_than_price := lower_than_price_value; higher_than_price := higher_than_price_value; cancel_group_id := cancel_group_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PendingMassCancelMessage.

  Module ExecutionReportCanceledMessage.

    (** ExecutionReport_CanceledMessage *)
    Record t := {
      sending_time : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      order_id : N;
      exec_id : N;
      ord_status : N;
      leaves_qty : N;
      cum_qty : N;
      cancel_reason : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (cancel_reason record < 256 ^ N.of_nat 1)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 1 (cancel_reason record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (orig_cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (ord_status_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cum_qty_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (cancel_reason_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (transact_time_value, bytes) =>
                                              Some ({| sending_time := sending_time_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; order_id := order_id_value; exec_id := exec_id_value; ord_status := ord_status_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; cancel_reason := cancel_reason_value; transact_time := transact_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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

  End ExecutionReportCanceledMessage.

  Module MassCancelDoneMessage.

    (** MassCancelDoneMessage *)
    Record t := {
      sending_time : N;
      cl_ord_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_bytes 16 (cl_ord_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              Some ({| sending_time := sending_time_value; cl_ord_id := cl_ord_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelDoneMessage.

  Module ExecutionReportPendingReplaceMessage.

    (** ExecutionReport_PendingReplaceMessage *)
    Record t := {
      sending_time : N;
      order_id : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : N;
      symbol : list byte;
      symbol_sfx : list byte;
      side : N;
      order_qty : N;
      ord_type : N;
      price : N;
      display_qty : N;
      locate_reqd : list byte;
      ord_status : N;
      leaves_qty : N;
      cum_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (locate_reqd record) = 1 /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_bytes 1 (locate_reqd record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (symbol_sfx_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (order_qty_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (display_qty_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (locate_reqd_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (ord_status_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (leaves_qty_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (cum_qty_value, bytes) =>
                                                                      Some ({| sending_time := sending_time_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; side := side_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; display_qty := display_qty_value; locate_reqd := locate_reqd_value; ord_status := ord_status_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionReportPendingReplaceMessage.

  Module ExecutionReportReplacedMessage.

    (** ExecutionReport_ReplacedMessage *)
    Record t := {
      sending_time : N;
      order_id : N;
      cl_ord_id : list byte;
      orig_cl_ord_id : list byte;
      exec_id : N;
      symbol : list byte;
      symbol_sfx : list byte;
      side : N;
      order_qty : N;
      ord_type : N;
      price : N;
      display_qty : N;
      locate_reqd : list byte;
      ord_status : N;
      leaves_qty : N;
      cum_qty : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (locate_reqd record) = 1 /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 1 (ord_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_bytes 1 (locate_reqd record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exec_id_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (symbol_sfx_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (order_qty_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (ord_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (display_qty_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (locate_reqd_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (ord_status_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (leaves_qty_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (cum_qty_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (transact_time_value, bytes) =>
                                                                          Some ({| sending_time := sending_time_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; exec_id := exec_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; side := side_value; order_qty := order_qty_value; ord_type := ord_type_value; price := price_value; display_qty := display_qty_value; locate_reqd := locate_reqd_value; ord_status := ord_status_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; transact_time := transact_time_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
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

  End ExecutionReportReplacedMessage.

  Module ExecutionReportTradeCorrectionMessage.

    (** ExecutionReport_TradeCorrectionMessage *)
    Record t := {
      sending_time : N;
      order_id : N;
      cl_ord_id : list byte;
      exec_id : N;
      exec_ref_id : N;
      trd_match_id : N;
      ord_status : N;
      last_px : N;
      last_qty_optional : N;
      leaves_qty : N;
      cum_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      (trd_match_id record < 256 ^ N.of_nat 8)%N /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty_optional record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_uint 8 (trd_match_id record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 16 bytes with
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
                          | Some (trd_match_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (ord_status_value, bytes) =>
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
                                                  Some ({| sending_time := sending_time_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; exec_ref_id := exec_ref_id_value; trd_match_id := trd_match_id_value; ord_status := ord_status_value; last_px := last_px_value; last_qty_optional := last_qty_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value |}, bytes)
                                              end
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

  End ExecutionReportTradeCorrectionMessage.

  Module ExecutionReportTradeBreakMessage.

    (** ExecutionReport_TradeBreakMessage *)
    Record t := {
      sending_time : N;
      order_id : N;
      cl_ord_id : list byte;
      exec_id : N;
      exec_ref_id : N;
      trd_match_id : N;
      ord_status : N;
      leaves_qty : N;
      cum_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (exec_ref_id record < 256 ^ N.of_nat 8)%N /\
      (trd_match_id record < 256 ^ N.of_nat 8)%N /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 8 (exec_ref_id record) ++
      encode_uint 8 (trd_match_id record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 16 bytes with
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
                          | Some (trd_match_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (ord_status_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (leaves_qty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (cum_qty_value, bytes) =>
                                          Some ({| sending_time := sending_time_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; exec_ref_id := exec_ref_id_value; trd_match_id := trd_match_id_value; ord_status := ord_status_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
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

  End ExecutionReportTradeBreakMessage.

  Module ExecutionReportRestatementMessage.

    (** ExecutionReport_RestatementMessage *)
    Record t := {
      sending_time : N;
      order_id : N;
      cl_ord_id : list byte;
      exec_id : N;
      ord_status : N;
      last_px_optional : N;
      leaves_qty : N;
      cum_qty : N;
      last_shares : N;
      exec_restatement_reason : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (ord_status record < 256 ^ N.of_nat 1)%N /\
      (last_px_optional record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (last_shares record < 256 ^ N.of_nat 4)%N /\
      (exec_restatement_reason record < 256 ^ N.of_nat 1)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 8 (exec_id record) ++
      encode_uint 1 (ord_status record) ++
      encode_uint 8 (last_px_optional record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 4 (last_shares record) ++
      encode_uint 1 (exec_restatement_reason record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (ord_status_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_px_optional_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cum_qty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_shares_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (exec_restatement_reason_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (transact_time_value, bytes) =>
                                                  Some ({| sending_time := sending_time_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; exec_id := exec_id_value; ord_status := ord_status_value; last_px_optional := last_px_optional_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; last_shares := last_shares_value; exec_restatement_reason := exec_restatement_reason_value; transact_time := transact_time_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
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

  End ExecutionReportRestatementMessage.

  Module OrderCancelRejectMessage.

    (** OrderCancelRejectMessage *)
    Record t := {
      sending_time : N;
      cl_ord_id : list byte;
      cxl_rej_response_to : N;
      cxl_rej_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (cxl_rej_response_to record < 256 ^ N.of_nat 1)%N /\
      (cxl_rej_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 1 (cxl_rej_response_to record) ++
      encode_uint 1 (cxl_rej_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (cxl_rej_response_to_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (cxl_rej_reason_value, bytes) =>
                      Some ({| sending_time := sending_time_value; cl_ord_id := cl_ord_id_value; cxl_rej_response_to := cxl_rej_response_to_value; cxl_rej_reason := cxl_rej_reason_value |}, bytes)
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

  End OrderCancelRejectMessage.

  Module MassCancelRejectMessage.

    (** MassCancelRejectMessage *)
    Record t := {
      sending_time : N;
      cl_ord_id : list byte;
      symbol : list byte;
      symbol_sfx : list byte;
      side : N;
      lower_than_price : N;
      higher_than_price : N;
      cancel_group_id : N;
      mass_cancel_reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (lower_than_price record < 256 ^ N.of_nat 8)%N /\
      (higher_than_price record < 256 ^ N.of_nat 8)%N /\
      (cancel_group_id record < 256 ^ N.of_nat 2)%N /\
      (mass_cancel_reject_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_uint 1 (side record) ++
      encode_uint 8 (lower_than_price record) ++
      encode_uint 8 (higher_than_price record) ++
      encode_uint 2 (cancel_group_id record) ++
      encode_uint 1 (mass_cancel_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (symbol_sfx_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (lower_than_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (higher_than_price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (cancel_group_id_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (mass_cancel_reject_reason_value, bytes) =>
                                          Some ({| sending_time := sending_time_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; side := side_value; lower_than_price := lower_than_price_value; higher_than_price := higher_than_price_value; cancel_group_id := cancel_group_id_value; mass_cancel_reject_reason := mass_cancel_reject_reason_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelRejectMessage.

End MemxEquitiesMemoV11Server.
