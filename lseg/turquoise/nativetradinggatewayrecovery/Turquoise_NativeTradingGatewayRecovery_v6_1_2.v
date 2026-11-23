From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * London Stock Exchange Native Trading Gateway Recovery

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
      - a length prefix framing what follows

    License: MIT No Attribution
  *)

Module TurquoiseNativeTradingGatewayRecoveryV612.

  Module MessageHeader.

    (** Native Trading Gateway Message Header *)
    Record t := {
      start_of_message : N;
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_of_message record < 256 ^ N.of_nat 1)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (start_of_message record) ++
      encode_uint_le 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (start_of_message_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (message_length_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  Some ({| start_of_message := start_of_message_value; message_length := message_length_value; message_type := message_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module LogonMessage.

    (** Allows the Participant and server to establish a session. *)
    Record t := {
      comp_id : list byte;
      password : list byte;
      new_password : list byte;
      message_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (comp_id record) = 25 /\
      Datatypes.length (password record) = 25 /\
      Datatypes.length (new_password record) = 25 /\
      (message_version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 25 (comp_id record) ++
      encode_bytes 25 (password record) ++
      encode_bytes 25 (new_password record) ++
      encode_uint 1 (message_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 25 bytes with
      | None => None
      | Some (comp_id_value, bytes) =>
          match decode_bytes 25 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 25 bytes with
              | None => None
              | Some (new_password_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (message_version_value, bytes) =>
                      Some ({| comp_id := comp_id_value; password := password_value; new_password := new_password_value; message_version := message_version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogonReplyMessage.

    (** Allows the server to acknowledge a Participant's Logon. *)
    Record t := {
      reject_code : N;
      password_expiry_day_count : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (password_expiry_day_count record) = 30.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (reject_code record) ++
      encode_bytes 30 (password_expiry_day_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (reject_code_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (password_expiry_day_count_value, bytes) =>
              Some ({| reject_code := reject_code_value; password_expiry_day_count := password_expiry_day_count_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonReplyMessage.

  Module LogoutMessage.

    (** Allows the Participant and server to terminate a session. *)
    Record t := {
      logout_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (logout_reason record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (logout_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (logout_reason_value, bytes) =>
          Some ({| logout_reason := logout_reason_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End LogoutMessage.

  Module MissedMessageRequestMessage.

    (** Allows the Participant to subscribe to missed messages through the Recovery Channel. *)
    Record t := {
      app_id : N;
      last_msg_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (app_id record < 256 ^ N.of_nat 1)%N /\
      (last_msg_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (app_id record) ++
      encode_uint_le 4 (last_msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (app_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (last_msg_seq_num_value, bytes) =>
              Some ({| app_id := app_id_value; last_msg_seq_num := last_msg_seq_num_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MissedMessageRequestMessage.

  Module MissedMessageRequestAckMessage.

    (** Allows the server to acknowledge a Participant's Missed Message Request. *)
    Record t := {
      missed_message_request_ack_response_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (missed_message_request_ack_response_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (missed_message_request_ack_response_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (missed_message_request_ack_response_type_value, bytes) =>
          Some ({| missed_message_request_ack_response_type := missed_message_request_ack_response_type_value |}, bytes)
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

  End MissedMessageRequestAckMessage.

  Module MissedMessageReportMessage.

    (** Allows the Server to communicate the result of a Missed Message Request. *)
    Record t := {
      missed_message_report_response_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (missed_message_report_response_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (missed_message_report_response_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (missed_message_report_response_type_value, bytes) =>
          Some ({| missed_message_report_response_type := missed_message_report_response_type_value |}, bytes)
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

  End MissedMessageReportMessage.

  Module RejectMessage.

    (** Allows the Server to reject a message that does not comply with the Native Trading Gateway messaging protocol. *)
    Record t := {
      reject_code : N;
      reject_reason : list byte;
      rejected_message_type : list byte;
      client_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reject_reason record) = 30 /\
      Datatypes.length (rejected_message_type record) = 1 /\
      Datatypes.length (client_order_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (reject_code record) ++
      encode_bytes 30 (reject_reason record) ++
      encode_bytes 1 (rejected_message_type record) ++
      encode_bytes 20 (client_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (reject_code_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (reject_reason_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (rejected_message_type_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (client_order_id_value, bytes) =>
                      Some ({| reject_code := reject_code_value; reject_reason := reject_reason_value; rejected_message_type := rejected_message_type_value; client_order_id := client_order_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RejectMessage.

  Module SystemStatusMessage.

    (** Sent to All Native Recovery Channel Participants on the event of Order Cache Outage. *)
    Record t := {
      app_id : N;
      app_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (app_id record < 256 ^ N.of_nat 1)%N /\
      (app_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (app_id record) ++
      encode_uint 1 (app_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (app_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (app_status_value, bytes) =>
              Some ({| app_id := app_id_value; app_status := app_status_value |}, bytes)
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

  End SystemStatusMessage.

  Module TransactTime.

    (** Composite *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (seconds record) ++
      encode_uint_le 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TransactTime.

  Module ExecutionReportMessage.

    (** Indicates order accepted, rejected, executed, expired, cancelled, cancel/replaced, trade cancel, BI triggered or pending cancel. *)
    Record t := {
      app_id : N;
      sequence_no : N;
      execution_id : list byte;
      client_order_id : list byte;
      order_id : list byte;
      exec_type : list byte;
      execution_report_ref_id : list byte;
      order_status : N;
      order_reject_code : N;
      executed_price : N;
      executed_qty : N;
      leaves_qty : N;
      waiver_flags : N;
      display_qty : N;
      common_symbol : list byte;
      side : N;
      secondary_order_id : N;
      counterparty : list byte;
      trade_liquidity_indicator : list byte;
      trade_match_id : N;
      transact_time : TransactTime.t;
      target_book : N;
      type_of_trade : N;
      capacity : N;
      reserved_1 : list byte;
      public_order_id : list byte;
      minimum_quantity : N;
      reputational_score : N;
      last_market : N;
      peg_price_type : N;
      owner_type : N;
      waiver_flags_2 : N;
      reserved_21 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (app_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_no record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (execution_id record) = 12 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (exec_type record) = 1 /\
      Datatypes.length (execution_report_ref_id record) = 12 /\
      (order_status record < 256 ^ N.of_nat 1)%N /\
      (order_reject_code record < 256 ^ N.of_nat 4)%N /\
      (executed_price record < 256 ^ N.of_nat 8)%N /\
      (executed_qty record < 256 ^ N.of_nat 4)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (waiver_flags record < 256 ^ N.of_nat 1)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (common_symbol record) = 8 /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (counterparty record) = 11 /\
      Datatypes.length (trade_liquidity_indicator record) = 1 /\
      (trade_match_id record < 256 ^ N.of_nat 8)%N /\
      TransactTime.bounded (transact_time record) /\
      (target_book record < 256 ^ N.of_nat 1)%N /\
      (type_of_trade record < 256 ^ N.of_nat 1)%N /\
      (capacity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (public_order_id record) = 12 /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N /\
      (reputational_score record < 256 ^ N.of_nat 1)%N /\
      (last_market record < 256 ^ N.of_nat 1)%N /\
      (peg_price_type record < 256 ^ N.of_nat 1)%N /\
      (owner_type record < 256 ^ N.of_nat 1)%N /\
      (waiver_flags_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_21 record) = 21.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (app_id record) ++
      encode_uint_le 4 (sequence_no record) ++
      encode_bytes 12 (execution_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_bytes 12 (execution_report_ref_id record) ++
      encode_uint 1 (order_status record) ++
      encode_uint_le 4 (order_reject_code record) ++
      encode_uint_le 8 (executed_price record) ++
      encode_uint_le 4 (executed_qty record) ++
      encode_uint_le 4 (leaves_qty record) ++
      encode_uint 1 (waiver_flags record) ++
      encode_uint_le 4 (display_qty record) ++
      encode_bytes 8 (common_symbol record) ++
      encode_uint 1 (side record) ++
      encode_uint_le 8 (secondary_order_id record) ++
      encode_bytes 11 (counterparty record) ++
      encode_bytes 1 (trade_liquidity_indicator record) ++
      encode_uint_le 8 (trade_match_id record) ++
      TransactTime.encode (transact_time record) ++
      encode_uint 1 (target_book record) ++
      encode_uint 1 (type_of_trade record) ++
      encode_uint 1 (capacity record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 12 (public_order_id record) ++
      encode_uint_le 4 (minimum_quantity record) ++
      encode_uint 1 (reputational_score record) ++
      encode_uint 1 (last_market record) ++
      encode_uint 1 (peg_price_type record) ++
      encode_uint 1 (owner_type record) ++
      encode_uint 1 (waiver_flags_2 record) ++
      encode_bytes 21 (reserved_21 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (app_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (sequence_no_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (execution_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (client_order_id_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (exec_type_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (execution_report_ref_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (order_status_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (order_reject_code_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (executed_price_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (executed_qty_value, bytes) =>
                                                  match decode_uint_le 4 bytes with
                                                  | None => None
                                                  | Some (leaves_qty_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (waiver_flags_value, bytes) =>
                                                          match decode_uint_le 4 bytes with
                                                          | None => None
                                                          | Some (display_qty_value, bytes) =>
                                                              match decode_bytes 8 bytes with
                                                              | None => None
                                                              | Some (common_symbol_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (side_value, bytes) =>
                                                                      match decode_uint_le 8 bytes with
                                                                      | None => None
                                                                      | Some (secondary_order_id_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (counterparty_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (trade_liquidity_indicator_value, bytes) =>
                                                                                  match decode_uint_le 8 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_match_id_value, bytes) =>
                                                                                      match TransactTime.decode bytes with
                                                                                      | None => None
                                                                                      | Some (transact_time_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (target_book_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (type_of_trade_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (capacity_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (reserved_1_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (public_order_id_value, bytes) =>
                                                                                                              match decode_uint_le 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (minimum_quantity_value, bytes) =>
                                                                                                                  match decode_uint 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (reputational_score_value, bytes) =>
                                                                                                                      match decode_uint 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (last_market_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (peg_price_type_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (owner_type_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (waiver_flags_2_value, bytes) =>
                                                                                                                                      match decode_bytes 21 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (reserved_21_value, bytes) =>
                                                                                                                                          Some ({| app_id := app_id_value; sequence_no := sequence_no_value; execution_id := execution_id_value; client_order_id := client_order_id_value; order_id := order_id_value; exec_type := exec_type_value; execution_report_ref_id := execution_report_ref_id_value; order_status := order_status_value; order_reject_code := order_reject_code_value; executed_price := executed_price_value; executed_qty := executed_qty_value; leaves_qty := leaves_qty_value; waiver_flags := waiver_flags_value; display_qty := display_qty_value; common_symbol := common_symbol_value; side := side_value; secondary_order_id := secondary_order_id_value; counterparty := counterparty_value; trade_liquidity_indicator := trade_liquidity_indicator_value; trade_match_id := trade_match_id_value; transact_time := transact_time_value; target_book := target_book_value; type_of_trade := type_of_trade_value; capacity := capacity_value; reserved_1 := reserved_1_value; public_order_id := public_order_id_value; minimum_quantity := minimum_quantity_value; reputational_score := reputational_score_value; last_market := last_market_value; peg_price_type := peg_price_type_value; owner_type := owner_type_value; waiver_flags_2 := waiver_flags_2_value; reserved_21 := reserved_21_value |}, bytes)
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 179.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length, !encode_bytes_length, !TransactTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint_le by exact bound_19.
      rewrite TransactTime.decode_encode by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint_le by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TransactTime.eq_dec]. Defined.

  End ExecutionReportMessage.

  Module OrderCancelRejectMessage.

    (** Indicates that an Order Cancel Request or Order Cancel/Replace Request has been rejected. *)
    Record t := {
      app_id : N;
      sequence_no : N;
      client_order_id : list byte;
      order_id : list byte;
      cancel_reject_reason : N;
      transact_time : TransactTime.t;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (app_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_no record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (order_id record) = 12 /\
      (cancel_reject_reason record < 256 ^ N.of_nat 4)%N /\
      TransactTime.bounded (transact_time record) /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (app_id record) ++
      encode_uint_le 4 (sequence_no record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 12 (order_id record) ++
      encode_uint_le 4 (cancel_reject_reason record) ++
      TransactTime.encode (transact_time record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (app_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (sequence_no_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (cancel_reject_reason_value, bytes) =>
                          match TransactTime.decode bytes with
                          | None => None
                          | Some (transact_time_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (reserved_10_value, bytes) =>
                                  Some ({| app_id := app_id_value; sequence_no := sequence_no_value; client_order_id := client_order_id_value; order_id := order_id_value; cancel_reject_reason := cancel_reject_reason_value; transact_time := transact_time_value; reserved_10 := reserved_10_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length, !encode_bytes_length, !TransactTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite TransactTime.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TransactTime.eq_dec]. Defined.

  End OrderCancelRejectMessage.

  Module OrderMassCancelReportMessage.

    (** Indicates a mass order cancel request was accepted or rejected. *)
    Record t := {
      app_id : N;
      sequence_no : N;
      client_order_id : list byte;
      mass_cancel_response : N;
      mass_cancel_reject_reason : N;
      reserved_4 : list byte;
      transact_time : TransactTime.t;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (app_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_no record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (client_order_id record) = 20 /\
      (mass_cancel_response record < 256 ^ N.of_nat 1)%N /\
      (mass_cancel_reject_reason record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_4 record) = 4 /\
      TransactTime.bounded (transact_time record) /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (app_id record) ++
      encode_uint_le 4 (sequence_no record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 1 (mass_cancel_response record) ++
      encode_uint_le 4 (mass_cancel_reject_reason record) ++
      encode_bytes 4 (reserved_4 record) ++
      TransactTime.encode (transact_time record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (app_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (sequence_no_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (mass_cancel_response_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (mass_cancel_reject_reason_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (reserved_4_value, bytes) =>
                              match TransactTime.decode bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (reserved_10_value, bytes) =>
                                      Some ({| app_id := app_id_value; sequence_no := sequence_no_value; client_order_id := client_order_id_value; mass_cancel_response := mass_cancel_response_value; mass_cancel_reject_reason := mass_cancel_reject_reason_value; reserved_4 := reserved_4_value; transact_time := transact_time_value; reserved_10 := reserved_10_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length, !encode_bytes_length, !TransactTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite TransactTime.decode_encode by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TransactTime.eq_dec]. Defined.

  End OrderMassCancelReportMessage.

  Module BusinessRejectMessage.

    (** Indicates that an application message could not be processed. *)
    Record t := {
      app_id : N;
      sequence_no : N;
      reject_code : N;
      client_order_id : list byte;
      order_id : list byte;
      transact_time : TransactTime.t;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (app_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_no record < 256 ^ N.of_nat 4)%N /\
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (order_id record) = 12 /\
      TransactTime.bounded (transact_time record) /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (app_id record) ++
      encode_uint_le 4 (sequence_no record) ++
      encode_uint_le 4 (reject_code record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 12 (order_id record) ++
      TransactTime.encode (transact_time record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (app_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (sequence_no_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (reject_code_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (client_order_id_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match TransactTime.decode bytes with
                          | None => None
                          | Some (transact_time_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (reserved_10_value, bytes) =>
                                  Some ({| app_id := app_id_value; sequence_no := sequence_no_value; reject_code := reject_code_value; client_order_id := client_order_id_value; order_id := order_id_value; transact_time := transact_time_value; reserved_10 := reserved_10_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length, !encode_bytes_length, !TransactTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite TransactTime.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TransactTime.eq_dec]. Defined.

  End BusinessRejectMessage.

End TurquoiseNativeTradingGatewayRecoveryV612.
