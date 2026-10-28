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
      - a field read in bits
      - a Composite rule
  *)

Module LsegMillenniumNativeTradingGatewayRecoveryV212.

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
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (start_of_message_value, bytes) =>
          match decode_uint 2 bytes with
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module LogonMessage.

    (** Allows the client and server to establish a session. *)
    Record t := {
      user_name : list byte;
      password : list byte;
      new_password : list byte;
      message_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_name record) = 25 /\
      Datatypes.length (password record) = 25 /\
      Datatypes.length (new_password record) = 25 /\
      (message_version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 25 (user_name record) ++
      encode_bytes 25 (password record) ++
      encode_bytes 25 (new_password record) ++
      encode_uint 1 (message_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 25 bytes with
      | None => None
      | Some (user_name_value, bytes) =>
          match decode_bytes 25 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 25 bytes with
              | None => None
              | Some (new_password_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (message_version_value, bytes) =>
                      Some ({| user_name := user_name_value; password := password_value; new_password := new_password_value; message_version := message_version_value |}, bytes)
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

    (** Allows the server to acknowledge a client's Logon. *)
    Record t := {
      reject_code : N;
      password_expiry_day_count : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (password_expiry_day_count record) = 30.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reject_code record) ++
      encode_bytes 30 (password_expiry_day_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
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

  End LogonReplyMessage.

  Module LogoutMessage.

    (** Allows the client and server to terminate a session. *)
    Record t := {
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          Some ({| reason := reason_value |}, bytes)
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

    (** Allows the client to subscribe to missed messages through the Recovery Channel. *)
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
      encode_uint 4 (last_msg_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (app_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (last_msg_seq_num_value, bytes) =>
              Some ({| app_id := app_id_value; last_msg_seq_num := last_msg_seq_num_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End MissedMessageRequestMessage.

  Module MissedMessageRequestAckMessage.

    (** Allows the server to acknowledge a client's Missed Message Request. *)
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

    (** Allows the server to communicate the result of a Missed Message Request. *)
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

    (** Used to reject a message that does not comply with the Native Trading Gateway messaging protocol. *)
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
      encode_uint 4 (reject_code record) ++
      encode_bytes 30 (reject_reason record) ++
      encode_bytes 1 (rejected_message_type record) ++
      encode_bytes 20 (client_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RejectMessage.

  Module SystemStatusMessage.

    (** Indicates service non availability of a partition, disseminated on the recovery and realtime channels. *)
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

  Module QuoteStatusReportMessage.

    (** Allows the server to communicate the status of the RFQ to the Requester. *)
    Record t := {
      partition_id : N;
      sequence_number : N;
      quote_msg_id : list byte;
      quote_req_id : list byte;
      quote_status : N;
      reject_code : N;
      order_book : N;
      market_makers : list byte;
      rfq_id : list byte;
      expire_time : N;
      bid_id : list byte;
      offer_id : list byte;
      expire_time_milliseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_msg_id record) = 20 /\
      Datatypes.length (quote_req_id record) = 10 /\
      (quote_status record < 256 ^ N.of_nat 1)%N /\
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_makers record) = 60 /\
      Datatypes.length (rfq_id record) = 10 /\
      (expire_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bid_id record) = 12 /\
      Datatypes.length (offer_id record) = 12 /\
      (expire_time_milliseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (partition_id record) ++
      encode_uint 4 (sequence_number record) ++
      encode_bytes 20 (quote_msg_id record) ++
      encode_bytes 10 (quote_req_id record) ++
      encode_uint 1 (quote_status record) ++
      encode_uint 4 (reject_code record) ++
      encode_uint 1 (order_book record) ++
      encode_bytes 60 (market_makers record) ++
      encode_bytes 10 (rfq_id record) ++
      encode_uint 4 (expire_time record) ++
      encode_bytes 12 (bid_id record) ++
      encode_bytes 12 (offer_id record) ++
      encode_uint 4 (expire_time_milliseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (partition_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (quote_msg_id_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (quote_req_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (quote_status_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (reject_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_book_value, bytes) =>
                                  match decode_bytes 60 bytes with
                                  | None => None
                                  | Some (market_makers_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (rfq_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (expire_time_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (bid_id_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (offer_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (expire_time_milliseconds_value, bytes) =>
                                                          Some ({| partition_id := partition_id_value; sequence_number := sequence_number_value; quote_msg_id := quote_msg_id_value; quote_req_id := quote_req_id_value; quote_status := quote_status_value; reject_code := reject_code_value; order_book := order_book_value; market_makers := market_makers_value; rfq_id := rfq_id_value; expire_time := expire_time_value; bid_id := bid_id_value; offer_id := offer_id_value; expire_time_milliseconds := expire_time_milliseconds_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 143.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteStatusReportMessage.

  Module QuoteRequestRejectMessage.

    (** Rejects an RFQ. Sent by the Market Maker to reject, and by the server to reject or to relay a Market Maker rejection. *)
    Record t := {
      partition_id : N;
      sequence_number : N;
      quote_req_id : list byte;
      reject_code : N;
      order_book : N;
      instrument_id : N;
      side : N;
      order_quantity : N;
      market_makers : list byte;
      contra_trader : list byte;
      rfq_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_req_id record) = 10 /\
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (order_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_makers record) = 60 /\
      Datatypes.length (contra_trader record) = 11 /\
      Datatypes.length (rfq_id record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (partition_id record) ++
      encode_uint 4 (sequence_number record) ++
      encode_bytes 10 (quote_req_id record) ++
      encode_uint 4 (reject_code record) ++
      encode_uint 1 (order_book record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (order_quantity record) ++
      encode_bytes 60 (market_makers record) ++
      encode_bytes 11 (contra_trader record) ++
      encode_bytes 10 (rfq_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (partition_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (quote_req_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (reject_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (order_book_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_quantity_value, bytes) =>
                                      match decode_bytes 60 bytes with
                                      | None => None
                                      | Some (market_makers_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (contra_trader_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (rfq_id_value, bytes) =>
                                                  Some ({| partition_id := partition_id_value; sequence_number := sequence_number_value; quote_req_id := quote_req_id_value; reject_code := reject_code_value; order_book := order_book_value; instrument_id := instrument_id_value; side := side_value; order_quantity := order_quantity_value; market_makers := market_makers_value; contra_trader := contra_trader_value; rfq_id := rfq_id_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 110.
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRequestRejectMessage.

  Module QuoteAckMessage.

    (** Allows the server to acknowledge a new or modified RFQ Quote to the Market Maker. *)
    Record t := {
      partition_id : N;
      sequence_number : N;
      quote_msg_id : list byte;
      rfq_id : list byte;
      bid_id : list byte;
      offer_id : list byte;
      quote_ack_status : N;
      reject_code : N;
      order_book : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_msg_id record) = 20 /\
      Datatypes.length (rfq_id record) = 10 /\
      Datatypes.length (bid_id record) = 12 /\
      Datatypes.length (offer_id record) = 12 /\
      (quote_ack_status record < 256 ^ N.of_nat 1)%N /\
      (reject_code record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (partition_id record) ++
      encode_uint 4 (sequence_number record) ++
      encode_bytes 20 (quote_msg_id record) ++
      encode_bytes 10 (rfq_id record) ++
      encode_bytes 12 (bid_id record) ++
      encode_bytes 12 (offer_id record) ++
      encode_uint 1 (quote_ack_status record) ++
      encode_uint 4 (reject_code record) ++
      encode_uint 1 (order_book record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (partition_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (quote_msg_id_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (rfq_id_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (bid_id_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (offer_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (quote_ack_status_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (reject_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_book_value, bytes) =>
                                          Some ({| partition_id := partition_id_value; sequence_number := sequence_number_value; quote_msg_id := quote_msg_id_value; rfq_id := rfq_id_value; bid_id := bid_id_value; offer_id := offer_id_value; quote_ack_status := quote_ack_status_value; reject_code := reject_code_value; order_book := order_book_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteAckMessage.

  Module QuoteResponseMessage.

    (** Carries an RFQ response. Sent by the Requester to execute or cancel an RFQ Quote, and by the server to report quote and RFQ status. *)
    Record t := {
      partition_id : N;
      sequence_number : N;
      quote_msg_id : list byte;
      rfq_id : list byte;
      quote_resp_type : N;
      instrument_id : N;
      side : N;
      order_quantity : N;
      limit_price : N;
      order_book : N;
      bid_id : list byte;
      offer_id : list byte;
      capacity : N;
      clearing_account : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_msg_id record) = 20 /\
      Datatypes.length (rfq_id record) = 10 /\
      (quote_resp_type record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (order_quantity record < 256 ^ N.of_nat 4)%N /\
      (limit_price record < 256 ^ N.of_nat 8)%N /\
      (order_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (bid_id record) = 12 /\
      Datatypes.length (offer_id record) = 12 /\
      (capacity record < 256 ^ N.of_nat 1)%N /\
      (clearing_account record < 256 ^ N.of_nat 1)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (partition_id record) ++
      encode_uint 4 (sequence_number record) ++
      encode_bytes 20 (quote_msg_id record) ++
      encode_bytes 10 (rfq_id record) ++
      encode_uint 1 (quote_resp_type record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (order_quantity record) ++
      encode_uint 8 (limit_price record) ++
      encode_uint 1 (order_book record) ++
      encode_bytes 12 (bid_id record) ++
      encode_bytes 12 (offer_id record) ++
      encode_uint 1 (capacity record) ++
      encode_uint 1 (clearing_account record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (partition_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (quote_msg_id_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (rfq_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (quote_resp_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_quantity_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (limit_price_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (order_book_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (bid_id_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (offer_id_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (capacity_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (clearing_account_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (reserved_8_value, bytes) =>
                                                                  Some ({| partition_id := partition_id_value; sequence_number := sequence_number_value; quote_msg_id := quote_msg_id_value; rfq_id := rfq_id_value; quote_resp_type := quote_resp_type_value; instrument_id := instrument_id_value; side := side_value; order_quantity := order_quantity_value; limit_price := limit_price_value; order_book := order_book_value; bid_id := bid_id_value; offer_id := offer_id_value; capacity := capacity_value; clearing_account := clearing_account_value; reserved_8 := reserved_8_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteResponseMessage.

End LsegMillenniumNativeTradingGatewayRecoveryV212.
