From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsas y Mercados Españoles BME Fixed Income Replay

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
      - a run counted by a field
  *)

Module BmeFixedIncomeReplayV16.

  Module MessageHeader.

    (** What every message carries, in either direction: its length and its type. Section 2.1 gives a published message a third field, the sequence number that lets a listener continue an interrupted session without gaps and without repeated messages, and the message tables state it as the message's own first field - which is where it is declared, since a client's Logon, Replay Request and Logout do not carry one *)
    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module LogonResponseMessage.

    (** The Logon Response message is used by the Server to accept a new session. In this message the sequence number will always be 0 *)
    Record t := {
      sequence_number : N;
      heart_bt_int : N;
      protocol_version : list byte;
      test_production_ind : list byte;
      environment_code : list byte;
      session_date : N;
      expected_sequence_number : N;
      sequence_number_to : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (heart_bt_int record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (protocol_version record) = 6 /\
      Datatypes.length (test_production_ind record) = 1 /\
      Datatypes.length (environment_code record) = 2 /\
      (session_date record < 256 ^ N.of_nat 4)%N /\
      (expected_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (sequence_number_to record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (heart_bt_int record) ++
      encode_bytes 6 (protocol_version record) ++
      encode_bytes 1 (test_production_ind record) ++
      encode_bytes 2 (environment_code record) ++
      encode_uint 4 (session_date record) ++
      encode_uint 4 (expected_sequence_number record) ++
      encode_uint 4 (sequence_number_to record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (heart_bt_int_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (protocol_version_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (test_production_ind_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (environment_code_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (session_date_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (expected_sequence_number_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (sequence_number_to_value, bytes) =>
                                      Some ({| sequence_number := sequence_number_value; heart_bt_int := heart_bt_int_value; protocol_version := protocol_version_value; test_production_ind := test_production_ind_value; environment_code := environment_code_value; session_date := session_date_value; expected_sequence_number := expected_sequence_number_value; sequence_number_to := sequence_number_to_value |}, bytes)
                                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonResponseMessage.

  Module LogoutResponseMessage.

    (** The Logout message is used by the Server to notify the end of a session, whether it is solicited or unsolicited. It may also be the answer to a failed logon attempt (see Logon message) *)
    Record t := {
      sequence_number : N;
      logout_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (logout_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (logout_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (logout_reason_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; logout_reason := logout_reason_value |}, bytes)
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

  End LogoutResponseMessage.

  Module HeartbeatMessage.

    (** The Heartbeat message is used by the Server to indicate that the communication is active. In the Heartbeat message, the SequenceNumber of the previously received message will be repeated *)
    Record t := {
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          Some ({| sequence_number := sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End HeartbeatMessage.

  Module NetworkStatusMessage.

    (** Message sent by the server with information about the connectivity between the Server and the central systems. In the Network Status message, the SequenceNumber of the previously received message will be repeated *)
    Record t := {
      sequence_number : N;
      network_status_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (network_status_value record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (network_status_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (network_status_value_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; network_status_value := network_status_value_value |}, bytes)
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

  End NetworkStatusMessage.

  Module LogonMessage.

    (** The Logon message is used to start a session by the client application *)
    Record t := {
      username : list byte;
      password : list byte;
      software_name : list byte;
      expected_sequence_number : N;
      subscriptions : N;
      protocol_version : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 7 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (software_name record) = 25 /\
      (expected_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (subscriptions record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (protocol_version record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 25 (software_name record) ++
      encode_uint 4 (expected_sequence_number record) ++
      encode_uint 1 (subscriptions record) ++
      encode_bytes 6 (protocol_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 25 bytes with
              | None => None
              | Some (software_name_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (expected_sequence_number_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (subscriptions_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (protocol_version_value, bytes) =>
                              Some ({| username := username_value; password := password_value; software_name := software_name_value; expected_sequence_number := expected_sequence_number_value; subscriptions := subscriptions_value; protocol_version := protocol_version_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module RejectMessage.

    (** It may be sent by the server to inform about the rejection of an unsupported or syntactically incorrect message. In the Reject message, the SequenceNumber of the previously received message will be repeated *)
    Record t := {
      sequence_number : N;
      session_reject_reason : N;
      text : list byte;
      msg_rejected_reference : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (session_reject_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (text record) = 58 /\
      (msg_rejected_reference record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (session_reject_reason record) ++
      encode_bytes 58 (text record) ++
      encode_uint 7 (msg_rejected_reference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (session_reject_reason_value, bytes) =>
              match decode_bytes 58 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  match decode_uint 7 bytes with
                  | None => None
                  | Some (msg_rejected_reference_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; session_reject_reason := session_reject_reason_value; text := text_value; msg_rejected_reference := msg_rejected_reference_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RejectMessage.

  Module ReplayRequestMessage.

    (** Message sent by the client application to request the replay of some specific UDP messages through the TCP Replay channel *)
    Record t := {
      sequence_number_from : N;
      sequence_number_to : N;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number_from record < 256 ^ N.of_nat 4)%N /\
      (sequence_number_to record < 256 ^ N.of_nat 4)%N /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number_from record) ++
      encode_uint 4 (sequence_number_to record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_from_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_to_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (request_id_value, bytes) =>
                  Some ({| sequence_number_from := sequence_number_from_value; sequence_number_to := sequence_number_to_value; request_id := request_id_value |}, bytes)
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

  End ReplayRequestMessage.

  Module ReplayRequestAckNackMessage.

    (** Message sent by the Replay Server as an inmediate answer to a Replay Request (Msg Type = 0x09). In this message the sequence number will always be 0 *)
    Record t := {
      sequence_number : N;
      sequence_number_from : N;
      sequence_number_to : N;
      request_id : N;
      status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (sequence_number_from record < 256 ^ N.of_nat 4)%N /\
      (sequence_number_to record < 256 ^ N.of_nat 4)%N /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (sequence_number_from record) ++
      encode_uint 4 (sequence_number_to record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_from_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (sequence_number_to_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (request_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (status_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; sequence_number_from := sequence_number_from_value; sequence_number_to := sequence_number_to_value; request_id := request_id_value; status := status_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End ReplayRequestAckNackMessage.

  Module TradingSessionStatusMessage.

    (** Sent by the server to inform about the session status in each Trading Mode *)
    Record t := {
      sequence_number : N;
      trading_session_id : N;
      trading_session_sub_id : N;
      trad_ses_status : N;
      transaction_date_and_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trading_session_sub_id record < 256 ^ N.of_nat 1)%N /\
      (trad_ses_status record < 256 ^ N.of_nat 1)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 1 (trading_session_sub_id record) ++
      encode_uint 1 (trad_ses_status record) ++
      encode_uint 8 (transaction_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (trading_session_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_sub_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trad_ses_status_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transaction_date_and_time_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; trading_session_id := trading_session_id_value; trading_session_sub_id := trading_session_sub_id_value; trad_ses_status := trad_ses_status_value; transaction_date_and_time := transaction_date_and_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End TradingSessionStatusMessage.

  Module NewsMessage.

    (** Used by the Server to communicate a Market Surveillance or system-wide text message *)
    Record t := {
      sequence_number : N;
      news_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (news_text record) = 78.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 78 (news_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 78 bytes with
          | None => None
          | Some (news_text_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; news_text := news_text_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 82.
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

  End NewsMessage.

  Module SecurityListCancellationReportMessage.

    (** Message sent by the server for cancelling previously defined securities *)
    Record t := {
      sequence_number : N;
      market_id : list byte;
      market_segment_id : list byte;
      security_code : N;
      symbol : list byte;
      symbol_isin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_id record) = 4 /\
      Datatypes.length (market_segment_id record) = 4 /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (symbol_isin record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 4 (market_id record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 12 (symbol_isin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_segment_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (symbol_isin_value, bytes) =>
                              Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityListCancellationReportMessage.

  Module SecurityListMessage.

    (** Message sent by the server to provide the definition of one security. It shares the same layout as the Security List Update Report message, but with a different Message Type *)
    Record t := {
      sequence_number : N;
      market_id : list byte;
      market_segment_id : list byte;
      security_code : N;
      symbol : list byte;
      symbol_isin : list byte;
      fisn : list byte;
      issuer_lei : list byte;
      security_group : list byte;
      cfi_code : list byte;
      security_type : list byte;
      maturity_date : N;
      issue_date : N;
      contract_multiplier : N;
      li_spre : N;
      sst_ipre : N;
      li_spost : N;
      sst_ipost : N;
      liquid_instrument : N;
      admission_requested_by_issuer : N;
      min_trade_vol : N;
      round_lot : N;
      currency : list byte;
      modality_mask_b_4 : N;
      security_description : list byte;
      trading_obligation : N;
      security_name : list byte;
      security_status : list byte;
      coupon_payment_date : N;
      min_price_increment : N;
      number_of_decimals : N;
      order_number_of_decimals : N;
      coupon_rate : N;
      issuer : list byte;
      trading_scope_b_1 : N;
      first_trading_date : N;
      settlement_system : list byte;
      maturity : N;
      coupon_periodicity : N;
      benchmark : N;
      strippable : N;
      volume_issued : N;
      alive_volume : N;
      coupon_type : list byte;
      coupon_quotation : N;
      accrued_interest_calculation_procedure : list byte;
      next_redemption_date : N;
      type_of_redemption : list byte;
      facial : N;
      calculation_method : list byte;
      date_last_coupon_was_paid : N;
      bond_seniority : list byte;
      interest_accrual_date : N;
      start_date : N;
      price_type : list byte;
      spread_to_index : N;
      benchmark_curve_points_units : list byte;
      benchmark_curve_points_value : N;
      benchmark_security_id : list byte;
      accrued_interest_rate_r_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_id record) = 4 /\
      Datatypes.length (market_segment_id record) = 4 /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (symbol_isin record) = 12 /\
      Datatypes.length (fisn record) = 35 /\
      Datatypes.length (issuer_lei record) = 20 /\
      Datatypes.length (security_group record) = 2 /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (security_type record) = 2 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (issue_date record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 8)%N /\
      (li_spre record < 256 ^ N.of_nat 8)%N /\
      (sst_ipre record < 256 ^ N.of_nat 8)%N /\
      (li_spost record < 256 ^ N.of_nat 8)%N /\
      (sst_ipost record < 256 ^ N.of_nat 8)%N /\
      (liquid_instrument record < 256 ^ N.of_nat 1)%N /\
      (admission_requested_by_issuer record < 256 ^ N.of_nat 1)%N /\
      (min_trade_vol record < 256 ^ N.of_nat 4)%N /\
      (round_lot record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 3 /\
      (modality_mask_b_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_description record) = 80 /\
      (trading_obligation record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_name record) = 40 /\
      Datatypes.length (security_status record) = 1 /\
      (coupon_payment_date record < 256 ^ N.of_nat 4)%N /\
      (min_price_increment record < 256 ^ N.of_nat 8)%N /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (coupon_rate record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issuer record) = 12 /\
      (trading_scope_b_1 record < 256 ^ N.of_nat 1)%N /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_system record) = 1 /\
      (maturity record < 256 ^ N.of_nat 8)%N /\
      (coupon_periodicity record < 256 ^ N.of_nat 1)%N /\
      (benchmark record < 256 ^ N.of_nat 1)%N /\
      (strippable record < 256 ^ N.of_nat 1)%N /\
      (volume_issued record < 256 ^ N.of_nat 8)%N /\
      (alive_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (coupon_type record) = 1 /\
      (coupon_quotation record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (accrued_interest_calculation_procedure record) = 1 /\
      (next_redemption_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (type_of_redemption record) = 2 /\
      (facial record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (calculation_method record) = 1 /\
      (date_last_coupon_was_paid record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bond_seniority record) = 4 /\
      (interest_accrual_date record < 256 ^ N.of_nat 4)%N /\
      (start_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_type record) = 1 /\
      (spread_to_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (benchmark_curve_points_units record) = 4 /\
      (benchmark_curve_points_value record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benchmark_security_id record) = 25 /\
      (accrued_interest_rate_r_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 4 (market_id record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 12 (symbol_isin record) ++
      encode_bytes 35 (fisn record) ++
      encode_bytes 20 (issuer_lei record) ++
      encode_bytes 2 (security_group record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 2 (security_type record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 4 (issue_date record) ++
      encode_uint 8 (contract_multiplier record) ++
      encode_uint 8 (li_spre record) ++
      encode_uint 8 (sst_ipre record) ++
      encode_uint 8 (li_spost record) ++
      encode_uint 8 (sst_ipost record) ++
      encode_uint 1 (liquid_instrument record) ++
      encode_uint 1 (admission_requested_by_issuer record) ++
      encode_uint 4 (min_trade_vol record) ++
      encode_uint 4 (round_lot record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 4 (modality_mask_b_4 record) ++
      encode_bytes 80 (security_description record) ++
      encode_uint 1 (trading_obligation record) ++
      encode_bytes 40 (security_name record) ++
      encode_bytes 1 (security_status record) ++
      encode_uint 4 (coupon_payment_date record) ++
      encode_uint 8 (min_price_increment record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_uint 8 (coupon_rate record) ++
      encode_bytes 12 (issuer record) ++
      encode_uint 1 (trading_scope_b_1 record) ++
      encode_uint 4 (first_trading_date record) ++
      encode_bytes 1 (settlement_system record) ++
      encode_uint 8 (maturity record) ++
      encode_uint 1 (coupon_periodicity record) ++
      encode_uint 1 (benchmark record) ++
      encode_uint 1 (strippable record) ++
      encode_uint 8 (volume_issued record) ++
      encode_uint 8 (alive_volume record) ++
      encode_bytes 1 (coupon_type record) ++
      encode_uint 1 (coupon_quotation record) ++
      encode_bytes 1 (accrued_interest_calculation_procedure record) ++
      encode_uint 4 (next_redemption_date record) ++
      encode_bytes 2 (type_of_redemption record) ++
      encode_uint 8 (facial record) ++
      encode_bytes 1 (calculation_method record) ++
      encode_uint 4 (date_last_coupon_was_paid record) ++
      encode_bytes 4 (bond_seniority record) ++
      encode_uint 4 (interest_accrual_date record) ++
      encode_uint 4 (start_date record) ++
      encode_bytes 1 (price_type record) ++
      encode_uint 8 (spread_to_index record) ++
      encode_bytes 4 (benchmark_curve_points_units record) ++
      encode_uint 1 (benchmark_curve_points_value record) ++
      encode_bytes 25 (benchmark_security_id record) ++
      encode_uint 8 (accrued_interest_rate_r_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_segment_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (symbol_isin_value, bytes) =>
                              match decode_bytes 35 bytes with
                              | None => None
                              | Some (fisn_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (issuer_lei_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (security_group_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (cfi_code_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (security_type_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (maturity_date_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (issue_date_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (contract_multiplier_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (li_spre_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (sst_ipre_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (li_spost_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (sst_ipost_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (liquid_instrument_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (admission_requested_by_issuer_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (min_trade_vol_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (round_lot_value, bytes) =>
                                                                                              match decode_bytes 3 bytes with
                                                                                              | None => None
                                                                                              | Some (currency_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (modality_mask_b_4_value, bytes) =>
                                                                                                      match decode_bytes 80 bytes with
                                                                                                      | None => None
                                                                                                      | Some (security_description_value, bytes) =>
                                                                                                          match decode_uint 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (trading_obligation_value, bytes) =>
                                                                                                              match decode_bytes 40 bytes with
                                                                                                              | None => None
                                                                                                              | Some (security_name_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (security_status_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (coupon_payment_date_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (min_price_increment_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (number_of_decimals_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (coupon_rate_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (issuer_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (trading_scope_b_1_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (first_trading_date_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (settlement_system_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (maturity_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (coupon_periodicity_value, bytes) =>
                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (benchmark_value, bytes) =>
                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (strippable_value, bytes) =>
                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (volume_issued_value, bytes) =>
                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (alive_volume_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (coupon_type_value, bytes) =>
                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (coupon_quotation_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (accrued_interest_calculation_procedure_value, bytes) =>
                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (next_redemption_date_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (type_of_redemption_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (facial_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (calculation_method_value, bytes) =>
                                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (date_last_coupon_was_paid_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (bond_seniority_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (interest_accrual_date_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (start_date_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (price_type_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (spread_to_index_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (benchmark_curve_points_units_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (benchmark_curve_points_value_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 25 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (benchmark_security_id_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (accrued_interest_rate_r_8_value, bytes) =>
                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; security_name := security_name_value; security_status := security_status_value; coupon_payment_date := coupon_payment_date_value; min_price_increment := min_price_increment_value; number_of_decimals := number_of_decimals_value; order_number_of_decimals := order_number_of_decimals_value; coupon_rate := coupon_rate_value; issuer := issuer_value; trading_scope_b_1 := trading_scope_b_1_value; first_trading_date := first_trading_date_value; settlement_system := settlement_system_value; maturity := maturity_value; coupon_periodicity := coupon_periodicity_value; benchmark := benchmark_value; strippable := strippable_value; volume_issued := volume_issued_value; alive_volume := alive_volume_value; coupon_type := coupon_type_value; coupon_quotation := coupon_quotation_value; accrued_interest_calculation_procedure := accrued_interest_calculation_procedure_value; next_redemption_date := next_redemption_date_value; type_of_redemption := type_of_redemption_value; facial := facial_value; calculation_method := calculation_method_value; date_last_coupon_was_paid := date_last_coupon_was_paid_value; bond_seniority := bond_seniority_value; interest_accrual_date := interest_accrual_date_value; start_date := start_date_value; price_type := price_type_value; spread_to_index := spread_to_index_value; benchmark_curve_points_units := benchmark_curve_points_units_value; benchmark_curve_points_value := benchmark_curve_points_value_value; benchmark_security_id := benchmark_security_id_value; accrued_interest_rate_r_8 := accrued_interest_rate_r_8_value |}, bytes)
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 450.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 bound_59]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_uint by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_bytes by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityListMessage.

  Module SecurityListUpdateReportMessage.

    (** Message sent by the server for reporting updates, during the session, to the security definition *)
    Record t := {
      sequence_number : N;
      market_id : list byte;
      market_segment_id : list byte;
      security_code : N;
      symbol : list byte;
      symbol_isin : list byte;
      fisn : list byte;
      issuer_lei : list byte;
      security_group : list byte;
      cfi_code : list byte;
      security_type : list byte;
      maturity_date : N;
      issue_date : N;
      contract_multiplier : N;
      li_spre : N;
      sst_ipre : N;
      li_spost : N;
      sst_ipost : N;
      liquid_instrument : N;
      admission_requested_by_issuer : N;
      min_trade_vol : N;
      round_lot : N;
      currency : list byte;
      modality_mask_b_4 : N;
      security_description : list byte;
      trading_obligation : N;
      security_name : list byte;
      security_status : list byte;
      coupon_payment_date : N;
      min_price_increment : N;
      number_of_decimals : N;
      order_number_of_decimals : N;
      coupon_rate : N;
      issuer : list byte;
      trading_scope_b_1 : N;
      first_trading_date : N;
      settlement_system : list byte;
      maturity : N;
      coupon_periodicity : N;
      benchmark : N;
      strippable : N;
      volume_issued : N;
      alive_volume : N;
      coupon_type : list byte;
      coupon_quotation : N;
      accrued_interest_calculation_procedure : list byte;
      next_redemption_date : N;
      type_of_redemption : list byte;
      facial : N;
      calculation_method : list byte;
      date_last_coupon_was_paid : N;
      bond_seniority : list byte;
      interest_accrual_date : N;
      start_date : N;
      price_type : list byte;
      spread_to_index : N;
      benchmark_curve_points_units : list byte;
      benchmark_curve_points_value : N;
      benchmark_security_id : list byte;
      accrued_interest_rate_r_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_id record) = 4 /\
      Datatypes.length (market_segment_id record) = 4 /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (symbol_isin record) = 12 /\
      Datatypes.length (fisn record) = 35 /\
      Datatypes.length (issuer_lei record) = 20 /\
      Datatypes.length (security_group record) = 2 /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (security_type record) = 2 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (issue_date record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 8)%N /\
      (li_spre record < 256 ^ N.of_nat 8)%N /\
      (sst_ipre record < 256 ^ N.of_nat 8)%N /\
      (li_spost record < 256 ^ N.of_nat 8)%N /\
      (sst_ipost record < 256 ^ N.of_nat 8)%N /\
      (liquid_instrument record < 256 ^ N.of_nat 1)%N /\
      (admission_requested_by_issuer record < 256 ^ N.of_nat 1)%N /\
      (min_trade_vol record < 256 ^ N.of_nat 4)%N /\
      (round_lot record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 3 /\
      (modality_mask_b_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_description record) = 80 /\
      (trading_obligation record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_name record) = 40 /\
      Datatypes.length (security_status record) = 1 /\
      (coupon_payment_date record < 256 ^ N.of_nat 4)%N /\
      (min_price_increment record < 256 ^ N.of_nat 8)%N /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (coupon_rate record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issuer record) = 12 /\
      (trading_scope_b_1 record < 256 ^ N.of_nat 1)%N /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_system record) = 1 /\
      (maturity record < 256 ^ N.of_nat 8)%N /\
      (coupon_periodicity record < 256 ^ N.of_nat 1)%N /\
      (benchmark record < 256 ^ N.of_nat 1)%N /\
      (strippable record < 256 ^ N.of_nat 1)%N /\
      (volume_issued record < 256 ^ N.of_nat 8)%N /\
      (alive_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (coupon_type record) = 1 /\
      (coupon_quotation record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (accrued_interest_calculation_procedure record) = 1 /\
      (next_redemption_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (type_of_redemption record) = 2 /\
      (facial record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (calculation_method record) = 1 /\
      (date_last_coupon_was_paid record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bond_seniority record) = 4 /\
      (interest_accrual_date record < 256 ^ N.of_nat 4)%N /\
      (start_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_type record) = 1 /\
      (spread_to_index record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (benchmark_curve_points_units record) = 4 /\
      (benchmark_curve_points_value record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benchmark_security_id record) = 25 /\
      (accrued_interest_rate_r_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 4 (market_id record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 12 (symbol_isin record) ++
      encode_bytes 35 (fisn record) ++
      encode_bytes 20 (issuer_lei record) ++
      encode_bytes 2 (security_group record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 2 (security_type record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 4 (issue_date record) ++
      encode_uint 8 (contract_multiplier record) ++
      encode_uint 8 (li_spre record) ++
      encode_uint 8 (sst_ipre record) ++
      encode_uint 8 (li_spost record) ++
      encode_uint 8 (sst_ipost record) ++
      encode_uint 1 (liquid_instrument record) ++
      encode_uint 1 (admission_requested_by_issuer record) ++
      encode_uint 4 (min_trade_vol record) ++
      encode_uint 4 (round_lot record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 4 (modality_mask_b_4 record) ++
      encode_bytes 80 (security_description record) ++
      encode_uint 1 (trading_obligation record) ++
      encode_bytes 40 (security_name record) ++
      encode_bytes 1 (security_status record) ++
      encode_uint 4 (coupon_payment_date record) ++
      encode_uint 8 (min_price_increment record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_uint 8 (coupon_rate record) ++
      encode_bytes 12 (issuer record) ++
      encode_uint 1 (trading_scope_b_1 record) ++
      encode_uint 4 (first_trading_date record) ++
      encode_bytes 1 (settlement_system record) ++
      encode_uint 8 (maturity record) ++
      encode_uint 1 (coupon_periodicity record) ++
      encode_uint 1 (benchmark record) ++
      encode_uint 1 (strippable record) ++
      encode_uint 8 (volume_issued record) ++
      encode_uint 8 (alive_volume record) ++
      encode_bytes 1 (coupon_type record) ++
      encode_uint 1 (coupon_quotation record) ++
      encode_bytes 1 (accrued_interest_calculation_procedure record) ++
      encode_uint 4 (next_redemption_date record) ++
      encode_bytes 2 (type_of_redemption record) ++
      encode_uint 8 (facial record) ++
      encode_bytes 1 (calculation_method record) ++
      encode_uint 4 (date_last_coupon_was_paid record) ++
      encode_bytes 4 (bond_seniority record) ++
      encode_uint 4 (interest_accrual_date record) ++
      encode_uint 4 (start_date record) ++
      encode_bytes 1 (price_type record) ++
      encode_uint 8 (spread_to_index record) ++
      encode_bytes 4 (benchmark_curve_points_units record) ++
      encode_uint 1 (benchmark_curve_points_value record) ++
      encode_bytes 25 (benchmark_security_id record) ++
      encode_uint 8 (accrued_interest_rate_r_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_segment_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (symbol_isin_value, bytes) =>
                              match decode_bytes 35 bytes with
                              | None => None
                              | Some (fisn_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (issuer_lei_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (security_group_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (cfi_code_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (security_type_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (maturity_date_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (issue_date_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (contract_multiplier_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (li_spre_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (sst_ipre_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (li_spost_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (sst_ipost_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (liquid_instrument_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (admission_requested_by_issuer_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (min_trade_vol_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (round_lot_value, bytes) =>
                                                                                              match decode_bytes 3 bytes with
                                                                                              | None => None
                                                                                              | Some (currency_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (modality_mask_b_4_value, bytes) =>
                                                                                                      match decode_bytes 80 bytes with
                                                                                                      | None => None
                                                                                                      | Some (security_description_value, bytes) =>
                                                                                                          match decode_uint 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (trading_obligation_value, bytes) =>
                                                                                                              match decode_bytes 40 bytes with
                                                                                                              | None => None
                                                                                                              | Some (security_name_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (security_status_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (coupon_payment_date_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (min_price_increment_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (number_of_decimals_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (coupon_rate_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (issuer_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (trading_scope_b_1_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (first_trading_date_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (settlement_system_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (maturity_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (coupon_periodicity_value, bytes) =>
                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (benchmark_value, bytes) =>
                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (strippable_value, bytes) =>
                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (volume_issued_value, bytes) =>
                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (alive_volume_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (coupon_type_value, bytes) =>
                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (coupon_quotation_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (accrued_interest_calculation_procedure_value, bytes) =>
                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (next_redemption_date_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (type_of_redemption_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (facial_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (calculation_method_value, bytes) =>
                                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (date_last_coupon_was_paid_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (bond_seniority_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (interest_accrual_date_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (start_date_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (price_type_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (spread_to_index_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (benchmark_curve_points_units_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (benchmark_curve_points_value_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 25 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (benchmark_security_id_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (accrued_interest_rate_r_8_value, bytes) =>
                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; security_name := security_name_value; security_status := security_status_value; coupon_payment_date := coupon_payment_date_value; min_price_increment := min_price_increment_value; number_of_decimals := number_of_decimals_value; order_number_of_decimals := order_number_of_decimals_value; coupon_rate := coupon_rate_value; issuer := issuer_value; trading_scope_b_1 := trading_scope_b_1_value; first_trading_date := first_trading_date_value; settlement_system := settlement_system_value; maturity := maturity_value; coupon_periodicity := coupon_periodicity_value; benchmark := benchmark_value; strippable := strippable_value; volume_issued := volume_issued_value; alive_volume := alive_volume_value; coupon_type := coupon_type_value; coupon_quotation := coupon_quotation_value; accrued_interest_calculation_procedure := accrued_interest_calculation_procedure_value; next_redemption_date := next_redemption_date_value; type_of_redemption := type_of_redemption_value; facial := facial_value; calculation_method := calculation_method_value; date_last_coupon_was_paid := date_last_coupon_was_paid_value; bond_seniority := bond_seniority_value; interest_accrual_date := interest_accrual_date_value; start_date := start_date_value; price_type := price_type_value; spread_to_index := spread_to_index_value; benchmark_curve_points_units := benchmark_curve_points_units_value; benchmark_curve_points_value := benchmark_curve_points_value_value; benchmark_security_id := benchmark_security_id_value; accrued_interest_rate_r_8 := accrued_interest_rate_r_8_value |}, bytes)
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 450.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 bound_59]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_uint by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_bytes by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityListUpdateReportMessage.

  Module SecurityStatusMessage.

    (** Message sent by the server to inform on the status of one security *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      reference_price : N;
      security_trading_status : N;
      non_availability_reason : N;
      high_limit_price : N;
      low_limit_price : N;
      static_range_type : list byte;
      order_static_range : N;
      block_static_range : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (non_availability_reason record < 256 ^ N.of_nat 1)%N /\
      (high_limit_price record < 256 ^ N.of_nat 8)%N /\
      (low_limit_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (static_range_type record) = 1 /\
      (order_static_range record < 256 ^ N.of_nat 8)%N /\
      (block_static_range record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 1 (non_availability_reason record) ++
      encode_uint 8 (high_limit_price record) ++
      encode_uint 8 (low_limit_price record) ++
      encode_bytes 1 (static_range_type record) ++
      encode_uint 8 (order_static_range record) ++
      encode_uint 8 (block_static_range record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (reference_price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (security_trading_status_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (non_availability_reason_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (high_limit_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (low_limit_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (static_range_type_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (order_static_range_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (block_static_range_value, bytes) =>
                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; reference_price := reference_price_value; security_trading_status := security_trading_status_value; non_availability_reason := non_availability_reason_value; high_limit_price := high_limit_price_value; low_limit_price := low_limit_price_value; static_range_type := static_range_type_value; order_static_range := order_static_range_value; block_static_range := block_static_range_value |}, bytes)
                                              end
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityStatusMessage.

  Module OrderBookClearMessage.

    (** Message sent by the UDP full-depth server whenever the information about order prices must be reset. In particular, it is sent by the server when the trading mode changes from auction to open market and vice versa *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value |}, bytes)
              end
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

  End OrderBookClearMessage.

  Module OrderMarketPreTransparencyInformationMessage.

    (** Used by the Server to communicate information about all active visible orders. During a session, any order is uniquely identified by the SecondaryOrderID *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      secondary_order_id : N;
      entry_date : N;
      side : list byte;
      priority : N;
      price : N;
      display_qty : N;
      alt_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (alt_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 8 (alt_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (secondary_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (entry_date_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (priority_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (display_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (alt_price_value, bytes) =>
                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; side := side_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderMarketPreTransparencyInformationMessage.

  Module QuoteMarketPreTransparencyInformationMessage.

    (** Used by the Server to communicate information about active quotes. In a session, a Quote is univoquely identified by its two orders: SecurityCode and SecondaryOrderID (buy order) and SecondaryOrderID2 (sell order) *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      secondary_order_id : N;
      secondary_order_id_2 : N;
      priority : N;
      price : N;
      display_qty : N;
      alt_price : N;
      priority_2 : N;
      price_2 : N;
      display_qty_2 : N;
      alt_price_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (alt_price record < 256 ^ N.of_nat 8)%N /\
      (priority_2 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 8)%N /\
      (display_qty_2 record < 256 ^ N.of_nat 4)%N /\
      (alt_price_2 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (secondary_order_id_2 record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 8 (alt_price record) ++
      encode_uint 4 (priority_2 record) ++
      encode_uint 8 (price_2 record) ++
      encode_uint 4 (display_qty_2 record) ++
      encode_uint 8 (alt_price_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (secondary_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (secondary_order_id_2_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (priority_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (display_qty_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (alt_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (priority_2_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_2_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (display_qty_2_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (alt_price_2_value, bytes) =>
                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; secondary_order_id_2 := secondary_order_id_2_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; alt_price_2 := alt_price_2_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End QuoteMarketPreTransparencyInformationMessage.

  Module OrderCancellationMarketMemberMessage.

    (** Used by the Server to communicate information order cancellation. The same message is used in Full-Depth data feeds (for order cancellations of any user), in the Order Entry Server (for cancellations of user orders) and in the Market & Order Server (for order cancellations of any user) *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      secondary_order_id : N;
      entry_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (secondary_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (entry_date_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End OrderCancellationMarketMemberMessage.

  Module QuoteCancellationMarketMemberMessage.

    (** Used by the Server to communicate information about quote cancellation. The same message is used in Full-Depth data feeds (for quote cancellations of any user), in the Order Entry Server (for cancellations of user quotes) and in the Market & Order Server (for quote cancellations of any user) *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      secondary_order_id : N;
      secondary_order_id_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id_2 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (secondary_order_id_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (secondary_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (secondary_order_id_2_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; secondary_order_id_2 := secondary_order_id_2_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End QuoteCancellationMarketMemberMessage.

  Module TradeMarketPostTransparencyInformationTopOfBookMessage.

    (** Used by the server to communicate trade information related to trades resulting from order matching in channels C/D and E/F. It is also used in channels A/B when the trade is the result of order matching at the end of an auction period (where only top-of-book information is shown) *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      market_segment_id : list byte;
      trading_session_id : N;
      trd_match_id : N;
      trade_type : list byte;
      last_px : N;
      last_qty : N;
      gross_trade_amt : N;
      designation : list byte;
      market_mechanism : list byte;
      algo_flag : N;
      alt_last_px : N;
      accrued_interest_amt : N;
      accrued_interest_rate_p_8 : N;
      settl_date : N;
      transaction_category : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_segment_id record) = 4 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (gross_trade_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (designation record) = 1 /\
      Datatypes.length (market_mechanism record) = 1 /\
      (algo_flag record < 256 ^ N.of_nat 1)%N /\
      (alt_last_px record < 256 ^ N.of_nat 8)%N /\
      (accrued_interest_amt record < 256 ^ N.of_nat 8)%N /\
      (accrued_interest_rate_p_8 record < 256 ^ N.of_nat 8)%N /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (gross_trade_amt record) ++
      encode_bytes 1 (designation record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_uint 1 (algo_flag record) ++
      encode_uint 8 (alt_last_px record) ++
      encode_uint 8 (accrued_interest_amt record) ++
      encode_uint 8 (accrued_interest_rate_p_8 record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trading_session_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trd_match_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (gross_trade_amt_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (designation_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (market_mechanism_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (algo_flag_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (alt_last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (accrued_interest_amt_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (accrued_interest_rate_p_8_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (settl_date_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (transaction_category_value, bytes) =>
                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMarketPostTransparencyInformationTopOfBookMessage.

  Module TradeTradeAmendmentOrCancellationMessage.

    (** Sent by the server to inform about a trade produced due to any reason other than order matching, also to inform about trades produced due to order matching in a Dark pool. In this message, all fields with the suffix 2 refer to the sell order, and the ones without the suffix refer either to both legs or the buy order *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      market_segment_id : list byte;
      trading_session_id : N;
      trd_match_id : N;
      trade_type : list byte;
      last_px : N;
      last_qty : N;
      gross_trade_amt : N;
      designation : list byte;
      market_mechanism : list byte;
      algo_flag : N;
      alt_last_px : N;
      accrued_interest_amt : N;
      accrued_interest_rate_p_8 : N;
      settl_date : N;
      transaction_category : list byte;
      last_change_flag : N;
      benc_rfpt_flag : list byte;
      trade_price_condition : list byte;
      pre_trade_transparency_waiver : list byte;
      deferral_waiver : list byte;
      post_deferral_publication_type : list byte;
      publish_date_and_time : N;
      trade_date : N;
      trade_session_date : N;
      settl_date_2 : N;
      end_cash : N;
      amended_trade_type : list byte;
      exec_ref_id : N;
      amended_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_segment_id record) = 4 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (gross_trade_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (designation record) = 1 /\
      Datatypes.length (market_mechanism record) = 1 /\
      (algo_flag record < 256 ^ N.of_nat 1)%N /\
      (alt_last_px record < 256 ^ N.of_nat 8)%N /\
      (accrued_interest_amt record < 256 ^ N.of_nat 8)%N /\
      (accrued_interest_rate_p_8 record < 256 ^ N.of_nat 8)%N /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (last_change_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benc_rfpt_flag record) = 1 /\
      Datatypes.length (trade_price_condition record) = 1 /\
      Datatypes.length (pre_trade_transparency_waiver record) = 1 /\
      Datatypes.length (deferral_waiver record) = 1 /\
      Datatypes.length (post_deferral_publication_type record) = 1 /\
      (publish_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (trade_session_date record < 256 ^ N.of_nat 4)%N /\
      (settl_date_2 record < 256 ^ N.of_nat 4)%N /\
      (end_cash record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (amended_trade_type record) = 1 /\
      (exec_ref_id record < 256 ^ N.of_nat 4)%N /\
      (amended_trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (gross_trade_amt record) ++
      encode_bytes 1 (designation record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_uint 1 (algo_flag record) ++
      encode_uint 8 (alt_last_px record) ++
      encode_uint 8 (accrued_interest_amt record) ++
      encode_uint 8 (accrued_interest_rate_p_8 record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 1 (last_change_flag record) ++
      encode_bytes 1 (benc_rfpt_flag record) ++
      encode_bytes 1 (trade_price_condition record) ++
      encode_bytes 1 (pre_trade_transparency_waiver record) ++
      encode_bytes 1 (deferral_waiver record) ++
      encode_bytes 1 (post_deferral_publication_type record) ++
      encode_uint 8 (publish_date_and_time record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 4 (trade_session_date record) ++
      encode_uint 4 (settl_date_2 record) ++
      encode_uint 8 (end_cash record) ++
      encode_bytes 1 (amended_trade_type record) ++
      encode_uint 4 (exec_ref_id record) ++
      encode_uint 4 (amended_trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trading_session_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trd_match_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (gross_trade_amt_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (designation_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (market_mechanism_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (algo_flag_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (alt_last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (accrued_interest_amt_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (accrued_interest_rate_p_8_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (settl_date_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (transaction_category_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (last_change_flag_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (benc_rfpt_flag_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (trade_price_condition_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (pre_trade_transparency_waiver_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (deferral_waiver_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (post_deferral_publication_type_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (publish_date_and_time_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (trade_date_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (trade_session_date_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (settl_date_2_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (end_cash_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (amended_trade_type_value, bytes) =>
                                                                                                                              match decode_uint 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (exec_ref_id_value, bytes) =>
                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (amended_trade_date_value, bytes) =>
                                                                                                                                      Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; post_deferral_publication_type := post_deferral_publication_type_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; settl_date_2 := settl_date_2_value; end_cash := end_cash_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value |}, bytes)
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 125.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 bound_31]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTradeAmendmentOrCancellationMessage.

  Module TradeMarketPostTransparencyInformationFullDepthMessage.

    (** Used by the server to communicate trade information related to trades resulting from order matching. The message also contains the situation in which the relevant orders will remain in the books *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      market_segment_id : list byte;
      trading_session_id : N;
      trd_match_id : N;
      trade_type : list byte;
      last_px : N;
      last_qty : N;
      gross_trade_amt : N;
      designation : list byte;
      market_mechanism : list byte;
      algo_flag : N;
      alt_last_px : N;
      accrued_interest_amt : N;
      accrued_interest_rate_p_8 : N;
      settl_date : N;
      transaction_category : list byte;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      alt_price : N;
      secondary_order_id_2 : N;
      entry_date_2 : N;
      priority_2 : N;
      price_2 : N;
      display_qty_2 : N;
      alt_price_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_segment_id record) = 4 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (gross_trade_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (designation record) = 1 /\
      Datatypes.length (market_mechanism record) = 1 /\
      (algo_flag record < 256 ^ N.of_nat 1)%N /\
      (alt_last_px record < 256 ^ N.of_nat 8)%N /\
      (accrued_interest_amt record < 256 ^ N.of_nat 8)%N /\
      (accrued_interest_rate_p_8 record < 256 ^ N.of_nat 8)%N /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (alt_price record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (entry_date_2 record < 256 ^ N.of_nat 4)%N /\
      (priority_2 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 8)%N /\
      (display_qty_2 record < 256 ^ N.of_nat 4)%N /\
      (alt_price_2 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (gross_trade_amt record) ++
      encode_bytes 1 (designation record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_uint 1 (algo_flag record) ++
      encode_uint 8 (alt_last_px record) ++
      encode_uint 8 (accrued_interest_amt record) ++
      encode_uint 8 (accrued_interest_rate_p_8 record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 8 (alt_price record) ++
      encode_uint 4 (secondary_order_id_2 record) ++
      encode_uint 4 (entry_date_2 record) ++
      encode_uint 4 (priority_2 record) ++
      encode_uint 8 (price_2 record) ++
      encode_uint 4 (display_qty_2 record) ++
      encode_uint 8 (alt_price_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trading_session_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trd_match_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (gross_trade_amt_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (designation_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (market_mechanism_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (algo_flag_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (alt_last_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (accrued_interest_amt_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (accrued_interest_rate_p_8_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (settl_date_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (transaction_category_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (secondary_order_id_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (entry_date_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (priority_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (price_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (display_qty_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (alt_price_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (secondary_order_id_2_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (entry_date_2_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (priority_2_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (price_2_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (display_qty_2_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (alt_price_2_value, bytes) =>
                                                                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; secondary_order_id_2 := secondary_order_id_2_value; entry_date_2 := entry_date_2_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; alt_price_2 := alt_price_2_value |}, bytes)
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 142.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 bound_29]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMarketPostTransparencyInformationFullDepthMessage.

  Module IndicationOfInterestMessage.

    (** Used by the Server to notify an indication of interest on a specific instrument. This functionality is available in Fixed Income and Derivatives *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      ioiid : N;
      ioi_trans_type : list byte;
      side : list byte;
      ioi_qty : N;
      ioi_price : N;
      trading_session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (ioiid record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ioi_trans_type record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (ioi_qty record < 256 ^ N.of_nat 4)%N /\
      (ioi_price record < 256 ^ N.of_nat 8)%N /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (ioiid record) ++
      encode_bytes 1 (ioi_trans_type record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (ioi_qty record) ++
      encode_uint 8 (ioi_price record) ++
      encode_uint 1 (trading_session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ioiid_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (ioi_trans_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (ioi_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (ioi_price_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (trading_session_id_value, bytes) =>
                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; ioiid := ioiid_value; ioi_trans_type := ioi_trans_type_value; side := side_value; ioi_qty := ioi_qty_value; ioi_price := ioi_price_value; trading_session_id := trading_session_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
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

  End IndicationOfInterestMessage.

  Module RfqMarketPreTransparencyInformationMessage.

    (** Used by the server to communicate price information about RFQs. The contents of the RFQID field match those of the field IOIID in the corresponding Indication of Interest message *)
    Record t := {
      sequence_number : N;
      rfqid : N;
      trading_session_id : N;
      security_code : N;
      transaction_date_and_time : N;
      mid_buy_price : N;
      mid_buy_volume : N;
      buy_rf_qs_number : N;
      mid_sell_price : N;
      mid_sell_volume : N;
      sell_rf_qs_number : N;
      bid_orders_1 : N;
      bid_size_1 : N;
      bid_px_1 : N;
      ask_orders_1 : N;
      ask_size_1 : N;
      ask_px_1 : N;
      bid_orders_2 : N;
      bid_size_2 : N;
      bid_px_2 : N;
      ask_orders_2 : N;
      ask_size_2 : N;
      ask_px_2 : N;
      bid_orders_3 : N;
      bid_size_3 : N;
      bid_px_3 : N;
      ask_orders_3 : N;
      ask_size_3 : N;
      ask_px_3 : N;
      bid_orders_4 : N;
      bid_size_4 : N;
      bid_px_4 : N;
      ask_orders_4 : N;
      ask_size_4 : N;
      ask_px_4 : N;
      bid_orders_5 : N;
      bid_size_5 : N;
      bid_px_5 : N;
      ask_orders_5 : N;
      ask_size_5 : N;
      ask_px_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (rfqid record < 256 ^ N.of_nat 4)%N /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (mid_buy_price record < 256 ^ N.of_nat 8)%N /\
      (mid_buy_volume record < 256 ^ N.of_nat 4)%N /\
      (buy_rf_qs_number record < 256 ^ N.of_nat 2)%N /\
      (mid_sell_price record < 256 ^ N.of_nat 8)%N /\
      (mid_sell_volume record < 256 ^ N.of_nat 4)%N /\
      (sell_rf_qs_number record < 256 ^ N.of_nat 2)%N /\
      (bid_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_1 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_1 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_2 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_2 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_2 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_2 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_2 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_2 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_3 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_3 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_3 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_3 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_3 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_3 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_4 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_4 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_4 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_4 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_4 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_4 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_5 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_5 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_5 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_5 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_5 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_5 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (rfqid record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 8 (mid_buy_price record) ++
      encode_uint 4 (mid_buy_volume record) ++
      encode_uint 2 (buy_rf_qs_number record) ++
      encode_uint 8 (mid_sell_price record) ++
      encode_uint 4 (mid_sell_volume record) ++
      encode_uint 2 (sell_rf_qs_number record) ++
      encode_uint 2 (bid_orders_1 record) ++
      encode_uint 4 (bid_size_1 record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 2 (ask_orders_1 record) ++
      encode_uint 4 (ask_size_1 record) ++
      encode_uint 8 (ask_px_1 record) ++
      encode_uint 2 (bid_orders_2 record) ++
      encode_uint 4 (bid_size_2 record) ++
      encode_uint 8 (bid_px_2 record) ++
      encode_uint 2 (ask_orders_2 record) ++
      encode_uint 4 (ask_size_2 record) ++
      encode_uint 8 (ask_px_2 record) ++
      encode_uint 2 (bid_orders_3 record) ++
      encode_uint 4 (bid_size_3 record) ++
      encode_uint 8 (bid_px_3 record) ++
      encode_uint 2 (ask_orders_3 record) ++
      encode_uint 4 (ask_size_3 record) ++
      encode_uint 8 (ask_px_3 record) ++
      encode_uint 2 (bid_orders_4 record) ++
      encode_uint 4 (bid_size_4 record) ++
      encode_uint 8 (bid_px_4 record) ++
      encode_uint 2 (ask_orders_4 record) ++
      encode_uint 4 (ask_size_4 record) ++
      encode_uint 8 (ask_px_4 record) ++
      encode_uint 2 (bid_orders_5 record) ++
      encode_uint 4 (bid_size_5 record) ++
      encode_uint 8 (bid_px_5 record) ++
      encode_uint 2 (ask_orders_5 record) ++
      encode_uint 4 (ask_size_5 record) ++
      encode_uint 8 (ask_px_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (rfqid_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transaction_date_and_time_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (mid_buy_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (mid_buy_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (buy_rf_qs_number_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (mid_sell_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (mid_sell_volume_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (sell_rf_qs_number_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (bid_orders_1_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (bid_size_1_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (bid_px_1_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (ask_orders_1_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (ask_size_1_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (ask_px_1_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (bid_orders_2_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (bid_size_2_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_px_2_value, bytes) =>
                                                                                      match decode_uint 2 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_orders_2_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_size_2_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_px_2_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_orders_3_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_size_3_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_px_3_value, bytes) =>
                                                                                                              match decode_uint 2 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_orders_3_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_size_3_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_px_3_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_orders_4_value, bytes) =>
                                                                                                                              match decode_uint 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_size_4_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_px_4_value, bytes) =>
                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_orders_4_value, bytes) =>
                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_size_4_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_px_4_value, bytes) =>
                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_orders_5_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_size_5_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_px_5_value, bytes) =>
                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_orders_5_value, bytes) =>
                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_size_5_value, bytes) =>
                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_px_5_value, bytes) =>
                                                                                                                                                                          Some ({| sequence_number := sequence_number_value; rfqid := rfqid_value; trading_session_id := trading_session_id_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; mid_buy_price := mid_buy_price_value; mid_buy_volume := mid_buy_volume_value; buy_rf_qs_number := buy_rf_qs_number_value; mid_sell_price := mid_sell_price_value; mid_sell_volume := mid_sell_volume_value; sell_rf_qs_number := sell_rf_qs_number_value; bid_orders_1 := bid_orders_1_value; bid_size_1 := bid_size_1_value; bid_px_1 := bid_px_1_value; ask_orders_1 := ask_orders_1_value; ask_size_1 := ask_size_1_value; ask_px_1 := ask_px_1_value; bid_orders_2 := bid_orders_2_value; bid_size_2 := bid_size_2_value; bid_px_2 := bid_px_2_value; ask_orders_2 := ask_orders_2_value; ask_size_2 := ask_size_2_value; ask_px_2 := ask_px_2_value; bid_orders_3 := bid_orders_3_value; bid_size_3 := bid_size_3_value; bid_px_3 := bid_px_3_value; ask_orders_3 := ask_orders_3_value; ask_size_3 := ask_size_3_value; ask_px_3 := ask_px_3_value; bid_orders_4 := bid_orders_4_value; bid_size_4 := bid_size_4_value; bid_px_4 := bid_px_4_value; ask_orders_4 := ask_orders_4_value; ask_size_4 := ask_size_4_value; ask_px_4 := ask_px_4_value; bid_orders_5 := bid_orders_5_value; bid_size_5 := bid_size_5_value; bid_px_5 := bid_px_5_value; ask_orders_5 := ask_orders_5_value; ask_size_5 := ask_size_5_value; ask_px_5 := ask_px_5_value |}, bytes)
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 bound_40]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
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
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RfqMarketPreTransparencyInformationMessage.

  Module TopOfBookMessage.

    (** Used by the UDP Servers to communicate Top-of-book price information during auctions. When there is an indicative match price, the fields BidPx1 and AskPx1 will have the same value *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      bid_orders_1 : N;
      bid_size_1 : N;
      bid_px_1 : N;
      alt_bid_px_1 : N;
      ask_orders_1 : N;
      ask_size_1 : N;
      ask_px_1 : N;
      alt_sell_px_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_1 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (alt_bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_1 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N /\
      (alt_sell_px_1 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 2 (bid_orders_1 record) ++
      encode_uint 4 (bid_size_1 record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 8 (alt_bid_px_1 record) ++
      encode_uint 2 (ask_orders_1 record) ++
      encode_uint 4 (ask_size_1 record) ++
      encode_uint 8 (ask_px_1 record) ++
      encode_uint 8 (alt_sell_px_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_orders_1_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_size_1_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_px_1_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (alt_bid_px_1_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ask_orders_1_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (ask_size_1_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (ask_px_1_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (alt_sell_px_1_value, bytes) =>
                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; bid_orders_1 := bid_orders_1_value; bid_size_1 := bid_size_1_value; bid_px_1 := bid_px_1_value; alt_bid_px_1 := alt_bid_px_1_value; ask_orders_1 := ask_orders_1_value; ask_size_1 := ask_size_1_value; ask_px_1 := ask_px_1_value; alt_sell_px_1 := alt_sell_px_1_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TopOfBookMessage.

End BmeFixedIncomeReplayV16.
