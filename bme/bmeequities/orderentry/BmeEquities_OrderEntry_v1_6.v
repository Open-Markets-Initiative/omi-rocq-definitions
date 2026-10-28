From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsas y Mercados Españoles BME Equities Order Entry

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

Module BmeEquitiesOrderEntryV16.

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
      text_c_58 : list byte;
      msg_rejected_reference : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (session_reject_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (text_c_58 record) = 58 /\
      (msg_rejected_reference record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (session_reject_reason record) ++
      encode_bytes 58 (text_c_58 record) ++
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
              | Some (text_c_58_value, bytes) =>
                  match decode_uint 7 bytes with
                  | None => None
                  | Some (msg_rejected_reference_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; session_reject_reason := session_reject_reason_value; text_c_58 := text_c_58_value; msg_rejected_reference := msg_rejected_reference_value |}, bytes)
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
      net_asset_value_identifier : list byte;
      security_sub_type : list byte;
      maturity_month_year : list byte;
      security_status : list byte;
      strike_price : N;
      strike_value : N;
      exercise_style : list byte;
      put_or_call : list byte;
      position_limit : N;
      nt_position_limit : N;
      issuer : list byte;
      cp_reg_type : N;
      barrier : N;
      last_trading_day : N;
      automatic_expiration : N;
      fee_type : list byte;
      barrier_2 : N;
      trigger_barrier : N;
      trigger_upper_barrier : N;
      average_quarterly_turnover : N;
      trading_scope : N;
      sicav_counterparty_member : list byte;
      net_asset_value_indicator : N;
      reference_trading_venue : list byte;
      outstanding_capital : N;
      first_trading_date : N;
      settlement_system : list byte;
      number_of_decimals : N;
      number_of_holders : N;
      outstanding_shares : N;
      minimum_authorized_shares : N;
      minimum_capital : N;
      last_admission_date : N;
      barrier_return : N;
      investment_fund_manager : list byte;
      effective_amount_filters_routed_orders : N;
      order_number_of_decimals : N;
      investment_fund_class : N;
      master_fund_name : list byte;
      investment_fund_management_company : list byte;
      investment_fund_depository : list byte;
      investment_fund_category : list byte;
      investment_fund_minimum_subscription_amount : N;
      investment_fund_minimum_maintenance_amount : N;
      investment_fund_cut_off_time : N;
      nav_communication_term : list byte;
      investment_fund_number_of_decimals : N;
      commodity_derivative_indicator : list byte;
      double_volume_cap_reached : N;
      adt : N;
      base_product : list byte;
      sub_product : list byte;
      further_sub_product : list byte;
      adnt : N;
      price_tick_rule : N;
      underlying_symbol : list byte;
      underlying_isin : list byte;
      underlying_currency : list byte;
      minimum_display_qty : N;
      retail_service_flag : N;
      self_match_prevention : N;
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
      Datatypes.length (net_asset_value_identifier record) = 7 /\
      Datatypes.length (security_sub_type record) = 2 /\
      Datatypes.length (maturity_month_year record) = 8 /\
      Datatypes.length (security_status record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exercise_style record) = 1 /\
      Datatypes.length (put_or_call record) = 1 /\
      (position_limit record < 256 ^ N.of_nat 8)%N /\
      (nt_position_limit record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issuer record) = 12 /\
      (cp_reg_type record < 256 ^ N.of_nat 1)%N /\
      (barrier record < 256 ^ N.of_nat 8)%N /\
      (last_trading_day record < 256 ^ N.of_nat 4)%N /\
      (automatic_expiration record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (fee_type record) = 2 /\
      (barrier_2 record < 256 ^ N.of_nat 8)%N /\
      (trigger_barrier record < 256 ^ N.of_nat 8)%N /\
      (trigger_upper_barrier record < 256 ^ N.of_nat 8)%N /\
      (average_quarterly_turnover record < 256 ^ N.of_nat 8)%N /\
      (trading_scope record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sicav_counterparty_member record) = 4 /\
      (net_asset_value_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference_trading_venue record) = 1 /\
      (outstanding_capital record < 256 ^ N.of_nat 8)%N /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_system record) = 1 /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (number_of_holders record < 256 ^ N.of_nat 4)%N /\
      (outstanding_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_authorized_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_capital record < 256 ^ N.of_nat 8)%N /\
      (last_admission_date record < 256 ^ N.of_nat 4)%N /\
      (barrier_return record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (investment_fund_manager record) = 80 /\
      (effective_amount_filters_routed_orders record < 256 ^ N.of_nat 8)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (investment_fund_class record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (master_fund_name record) = 80 /\
      Datatypes.length (investment_fund_management_company record) = 80 /\
      Datatypes.length (investment_fund_depository record) = 80 /\
      Datatypes.length (investment_fund_category record) = 80 /\
      (investment_fund_minimum_subscription_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_minimum_maintenance_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_cut_off_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (nav_communication_term record) = 1 /\
      (investment_fund_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_derivative_indicator record) = 1 /\
      (double_volume_cap_reached record < 256 ^ N.of_nat 1)%N /\
      (adt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_product record) = 4 /\
      Datatypes.length (sub_product record) = 4 /\
      Datatypes.length (further_sub_product record) = 4 /\
      (adnt record < 256 ^ N.of_nat 8)%N /\
      (price_tick_rule record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 22 /\
      Datatypes.length (underlying_isin record) = 12 /\
      Datatypes.length (underlying_currency record) = 3 /\
      (minimum_display_qty record < 256 ^ N.of_nat 4)%N /\
      (retail_service_flag record < 256 ^ N.of_nat 1)%N /\
      (self_match_prevention record < 256 ^ N.of_nat 1)%N.

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
      encode_bytes 7 (net_asset_value_identifier record) ++
      encode_bytes 2 (security_sub_type record) ++
      encode_bytes 8 (maturity_month_year record) ++
      encode_bytes 1 (security_status record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 8 (strike_value record) ++
      encode_bytes 1 (exercise_style record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_uint 8 (position_limit record) ++
      encode_uint 8 (nt_position_limit record) ++
      encode_bytes 12 (issuer record) ++
      encode_uint 1 (cp_reg_type record) ++
      encode_uint 8 (barrier record) ++
      encode_uint 4 (last_trading_day record) ++
      encode_uint 1 (automatic_expiration record) ++
      encode_bytes 2 (fee_type record) ++
      encode_uint 8 (barrier_2 record) ++
      encode_uint 8 (trigger_barrier record) ++
      encode_uint 8 (trigger_upper_barrier record) ++
      encode_uint 8 (average_quarterly_turnover record) ++
      encode_uint 1 (trading_scope record) ++
      encode_bytes 4 (sicav_counterparty_member record) ++
      encode_uint 1 (net_asset_value_indicator record) ++
      encode_bytes 1 (reference_trading_venue record) ++
      encode_uint 8 (outstanding_capital record) ++
      encode_uint 4 (first_trading_date record) ++
      encode_bytes 1 (settlement_system record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 4 (number_of_holders record) ++
      encode_uint 4 (outstanding_shares record) ++
      encode_uint 4 (minimum_authorized_shares record) ++
      encode_uint 8 (minimum_capital record) ++
      encode_uint 4 (last_admission_date record) ++
      encode_uint 8 (barrier_return record) ++
      encode_bytes 80 (investment_fund_manager record) ++
      encode_uint 8 (effective_amount_filters_routed_orders record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_uint 1 (investment_fund_class record) ++
      encode_bytes 80 (master_fund_name record) ++
      encode_bytes 80 (investment_fund_management_company record) ++
      encode_bytes 80 (investment_fund_depository record) ++
      encode_bytes 80 (investment_fund_category record) ++
      encode_uint 8 (investment_fund_minimum_subscription_amount record) ++
      encode_uint 8 (investment_fund_minimum_maintenance_amount record) ++
      encode_uint 8 (investment_fund_cut_off_time record) ++
      encode_bytes 1 (nav_communication_term record) ++
      encode_uint 1 (investment_fund_number_of_decimals record) ++
      encode_bytes 1 (commodity_derivative_indicator record) ++
      encode_uint 1 (double_volume_cap_reached record) ++
      encode_uint 8 (adt record) ++
      encode_bytes 4 (base_product record) ++
      encode_bytes 4 (sub_product record) ++
      encode_bytes 4 (further_sub_product record) ++
      encode_uint 8 (adnt record) ++
      encode_uint 1 (price_tick_rule record) ++
      encode_bytes 22 (underlying_symbol record) ++
      encode_bytes 12 (underlying_isin record) ++
      encode_bytes 3 (underlying_currency record) ++
      encode_uint 4 (minimum_display_qty record) ++
      encode_uint 1 (retail_service_flag record) ++
      encode_uint 1 (self_match_prevention record).

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
                                                                                                                  match decode_bytes 7 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (net_asset_value_identifier_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (security_sub_type_value, bytes) =>
                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (maturity_month_year_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (security_status_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (strike_value_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (exercise_style_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (put_or_call_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (position_limit_value, bytes) =>
                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (nt_position_limit_value, bytes) =>
                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (issuer_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (cp_reg_type_value, bytes) =>
                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (barrier_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (last_trading_day_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (automatic_expiration_value, bytes) =>
                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (fee_type_value, bytes) =>
                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (barrier_2_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (trigger_barrier_value, bytes) =>
                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (trigger_upper_barrier_value, bytes) =>
                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (average_quarterly_turnover_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (trading_scope_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (sicav_counterparty_member_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (net_asset_value_indicator_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (reference_trading_venue_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (outstanding_capital_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (first_trading_date_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (settlement_system_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (number_of_holders_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (outstanding_shares_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (minimum_authorized_shares_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (minimum_capital_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (last_admission_date_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (barrier_return_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (investment_fund_manager_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (effective_amount_filters_routed_orders_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (investment_fund_class_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (master_fund_name_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (investment_fund_management_company_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (investment_fund_depository_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (investment_fund_category_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (investment_fund_minimum_subscription_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (investment_fund_minimum_maintenance_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (investment_fund_cut_off_time_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (nav_communication_term_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (investment_fund_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (commodity_derivative_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (double_volume_cap_reached_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (adt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (base_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (further_sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (adnt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (price_tick_rule_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (underlying_symbol_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (underlying_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (underlying_currency_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (minimum_display_qty_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (retail_service_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (self_match_prevention_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; security_name := security_name_value; net_asset_value_identifier := net_asset_value_identifier_value; security_sub_type := security_sub_type_value; maturity_month_year := maturity_month_year_value; security_status := security_status_value; strike_price := strike_price_value; strike_value := strike_value_value; exercise_style := exercise_style_value; put_or_call := put_or_call_value; position_limit := position_limit_value; nt_position_limit := nt_position_limit_value; issuer := issuer_value; cp_reg_type := cp_reg_type_value; barrier := barrier_value; last_trading_day := last_trading_day_value; automatic_expiration := automatic_expiration_value; fee_type := fee_type_value; barrier_2 := barrier_2_value; trigger_barrier := trigger_barrier_value; trigger_upper_barrier := trigger_upper_barrier_value; average_quarterly_turnover := average_quarterly_turnover_value; trading_scope := trading_scope_value; sicav_counterparty_member := sicav_counterparty_member_value; net_asset_value_indicator := net_asset_value_indicator_value; reference_trading_venue := reference_trading_venue_value; outstanding_capital := outstanding_capital_value; first_trading_date := first_trading_date_value; settlement_system := settlement_system_value; number_of_decimals := number_of_decimals_value; number_of_holders := number_of_holders_value; outstanding_shares := outstanding_shares_value; minimum_authorized_shares := minimum_authorized_shares_value; minimum_capital := minimum_capital_value; last_admission_date := last_admission_date_value; barrier_return := barrier_return_value; investment_fund_manager := investment_fund_manager_value; effective_amount_filters_routed_orders := effective_amount_filters_routed_orders_value; order_number_of_decimals := order_number_of_decimals_value; investment_fund_class := investment_fund_class_value; master_fund_name := master_fund_name_value; investment_fund_management_company := investment_fund_management_company_value; investment_fund_depository := investment_fund_depository_value; investment_fund_category := investment_fund_category_value; investment_fund_minimum_subscription_amount := investment_fund_minimum_subscription_amount_value; investment_fund_minimum_maintenance_amount := investment_fund_minimum_maintenance_amount_value; investment_fund_cut_off_time := investment_fund_cut_off_time_value; nav_communication_term := nav_communication_term_value; investment_fund_number_of_decimals := investment_fund_number_of_decimals_value; commodity_derivative_indicator := commodity_derivative_indicator_value; double_volume_cap_reached := double_volume_cap_reached_value; adt := adt_value; base_product := base_product_value; sub_product := sub_product_value; further_sub_product := further_sub_product_value; adnt := adnt_value; price_tick_rule := price_tick_rule_value; underlying_symbol := underlying_symbol_value; underlying_isin := underlying_isin_value; underlying_currency := underlying_currency_value; minimum_display_qty := minimum_display_qty_value; retail_service_flag := retail_service_flag_value; self_match_prevention := self_match_prevention_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 976.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 bound_87]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_uint by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_uint by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_uint by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_uint by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_uint by exact bound_76.
      rewrite decode_encode_bytes by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_uint by exact bound_80.
      rewrite decode_encode_uint by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_bytes by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_uint by exact bound_86.
      rewrite decode_encode_uint by exact bound_87.
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
      net_asset_value_identifier : list byte;
      security_sub_type : list byte;
      maturity_month_year : list byte;
      security_status : list byte;
      strike_price : N;
      strike_value : N;
      exercise_style : list byte;
      put_or_call : list byte;
      position_limit : N;
      nt_position_limit : N;
      issuer : list byte;
      cp_reg_type : N;
      barrier : N;
      last_trading_day : N;
      automatic_expiration : N;
      fee_type : list byte;
      barrier_2 : N;
      trigger_barrier : N;
      trigger_upper_barrier : N;
      average_quarterly_turnover : N;
      trading_scope : N;
      sicav_counterparty_member : list byte;
      net_asset_value_indicator : N;
      reference_trading_venue : list byte;
      outstanding_capital : N;
      first_trading_date : N;
      settlement_system : list byte;
      number_of_decimals : N;
      number_of_holders : N;
      outstanding_shares : N;
      minimum_authorized_shares : N;
      minimum_capital : N;
      last_admission_date : N;
      barrier_return : N;
      investment_fund_manager : list byte;
      effective_amount_filters_routed_orders : N;
      order_number_of_decimals : N;
      investment_fund_class : N;
      master_fund_name : list byte;
      investment_fund_management_company : list byte;
      investment_fund_depository : list byte;
      investment_fund_category : list byte;
      investment_fund_minimum_subscription_amount : N;
      investment_fund_minimum_maintenance_amount : N;
      investment_fund_cut_off_time : N;
      nav_communication_term : list byte;
      investment_fund_number_of_decimals : N;
      commodity_derivative_indicator : list byte;
      double_volume_cap_reached : N;
      adt : N;
      base_product : list byte;
      sub_product : list byte;
      further_sub_product : list byte;
      adnt : N;
      price_tick_rule : N;
      underlying_symbol : list byte;
      underlying_isin : list byte;
      underlying_currency : list byte;
      minimum_display_qty : N;
      retail_service_flag : N;
      self_match_prevention : N;
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
      Datatypes.length (net_asset_value_identifier record) = 7 /\
      Datatypes.length (security_sub_type record) = 2 /\
      Datatypes.length (maturity_month_year record) = 8 /\
      Datatypes.length (security_status record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exercise_style record) = 1 /\
      Datatypes.length (put_or_call record) = 1 /\
      (position_limit record < 256 ^ N.of_nat 8)%N /\
      (nt_position_limit record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issuer record) = 12 /\
      (cp_reg_type record < 256 ^ N.of_nat 1)%N /\
      (barrier record < 256 ^ N.of_nat 8)%N /\
      (last_trading_day record < 256 ^ N.of_nat 4)%N /\
      (automatic_expiration record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (fee_type record) = 2 /\
      (barrier_2 record < 256 ^ N.of_nat 8)%N /\
      (trigger_barrier record < 256 ^ N.of_nat 8)%N /\
      (trigger_upper_barrier record < 256 ^ N.of_nat 8)%N /\
      (average_quarterly_turnover record < 256 ^ N.of_nat 8)%N /\
      (trading_scope record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sicav_counterparty_member record) = 4 /\
      (net_asset_value_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference_trading_venue record) = 1 /\
      (outstanding_capital record < 256 ^ N.of_nat 8)%N /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_system record) = 1 /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (number_of_holders record < 256 ^ N.of_nat 4)%N /\
      (outstanding_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_authorized_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_capital record < 256 ^ N.of_nat 8)%N /\
      (last_admission_date record < 256 ^ N.of_nat 4)%N /\
      (barrier_return record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (investment_fund_manager record) = 80 /\
      (effective_amount_filters_routed_orders record < 256 ^ N.of_nat 8)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (investment_fund_class record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (master_fund_name record) = 80 /\
      Datatypes.length (investment_fund_management_company record) = 80 /\
      Datatypes.length (investment_fund_depository record) = 80 /\
      Datatypes.length (investment_fund_category record) = 80 /\
      (investment_fund_minimum_subscription_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_minimum_maintenance_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_cut_off_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (nav_communication_term record) = 1 /\
      (investment_fund_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_derivative_indicator record) = 1 /\
      (double_volume_cap_reached record < 256 ^ N.of_nat 1)%N /\
      (adt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_product record) = 4 /\
      Datatypes.length (sub_product record) = 4 /\
      Datatypes.length (further_sub_product record) = 4 /\
      (adnt record < 256 ^ N.of_nat 8)%N /\
      (price_tick_rule record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 22 /\
      Datatypes.length (underlying_isin record) = 12 /\
      Datatypes.length (underlying_currency record) = 3 /\
      (minimum_display_qty record < 256 ^ N.of_nat 4)%N /\
      (retail_service_flag record < 256 ^ N.of_nat 1)%N /\
      (self_match_prevention record < 256 ^ N.of_nat 1)%N.

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
      encode_bytes 7 (net_asset_value_identifier record) ++
      encode_bytes 2 (security_sub_type record) ++
      encode_bytes 8 (maturity_month_year record) ++
      encode_bytes 1 (security_status record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 8 (strike_value record) ++
      encode_bytes 1 (exercise_style record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_uint 8 (position_limit record) ++
      encode_uint 8 (nt_position_limit record) ++
      encode_bytes 12 (issuer record) ++
      encode_uint 1 (cp_reg_type record) ++
      encode_uint 8 (barrier record) ++
      encode_uint 4 (last_trading_day record) ++
      encode_uint 1 (automatic_expiration record) ++
      encode_bytes 2 (fee_type record) ++
      encode_uint 8 (barrier_2 record) ++
      encode_uint 8 (trigger_barrier record) ++
      encode_uint 8 (trigger_upper_barrier record) ++
      encode_uint 8 (average_quarterly_turnover record) ++
      encode_uint 1 (trading_scope record) ++
      encode_bytes 4 (sicav_counterparty_member record) ++
      encode_uint 1 (net_asset_value_indicator record) ++
      encode_bytes 1 (reference_trading_venue record) ++
      encode_uint 8 (outstanding_capital record) ++
      encode_uint 4 (first_trading_date record) ++
      encode_bytes 1 (settlement_system record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 4 (number_of_holders record) ++
      encode_uint 4 (outstanding_shares record) ++
      encode_uint 4 (minimum_authorized_shares record) ++
      encode_uint 8 (minimum_capital record) ++
      encode_uint 4 (last_admission_date record) ++
      encode_uint 8 (barrier_return record) ++
      encode_bytes 80 (investment_fund_manager record) ++
      encode_uint 8 (effective_amount_filters_routed_orders record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_uint 1 (investment_fund_class record) ++
      encode_bytes 80 (master_fund_name record) ++
      encode_bytes 80 (investment_fund_management_company record) ++
      encode_bytes 80 (investment_fund_depository record) ++
      encode_bytes 80 (investment_fund_category record) ++
      encode_uint 8 (investment_fund_minimum_subscription_amount record) ++
      encode_uint 8 (investment_fund_minimum_maintenance_amount record) ++
      encode_uint 8 (investment_fund_cut_off_time record) ++
      encode_bytes 1 (nav_communication_term record) ++
      encode_uint 1 (investment_fund_number_of_decimals record) ++
      encode_bytes 1 (commodity_derivative_indicator record) ++
      encode_uint 1 (double_volume_cap_reached record) ++
      encode_uint 8 (adt record) ++
      encode_bytes 4 (base_product record) ++
      encode_bytes 4 (sub_product record) ++
      encode_bytes 4 (further_sub_product record) ++
      encode_uint 8 (adnt record) ++
      encode_uint 1 (price_tick_rule record) ++
      encode_bytes 22 (underlying_symbol record) ++
      encode_bytes 12 (underlying_isin record) ++
      encode_bytes 3 (underlying_currency record) ++
      encode_uint 4 (minimum_display_qty record) ++
      encode_uint 1 (retail_service_flag record) ++
      encode_uint 1 (self_match_prevention record).

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
                                                                                                                  match decode_bytes 7 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (net_asset_value_identifier_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (security_sub_type_value, bytes) =>
                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (maturity_month_year_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (security_status_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (strike_value_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (exercise_style_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (put_or_call_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (position_limit_value, bytes) =>
                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (nt_position_limit_value, bytes) =>
                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (issuer_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (cp_reg_type_value, bytes) =>
                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (barrier_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (last_trading_day_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (automatic_expiration_value, bytes) =>
                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (fee_type_value, bytes) =>
                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (barrier_2_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (trigger_barrier_value, bytes) =>
                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (trigger_upper_barrier_value, bytes) =>
                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (average_quarterly_turnover_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (trading_scope_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (sicav_counterparty_member_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (net_asset_value_indicator_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (reference_trading_venue_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (outstanding_capital_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (first_trading_date_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (settlement_system_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (number_of_holders_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (outstanding_shares_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (minimum_authorized_shares_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (minimum_capital_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (last_admission_date_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (barrier_return_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (investment_fund_manager_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (effective_amount_filters_routed_orders_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (investment_fund_class_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (master_fund_name_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (investment_fund_management_company_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (investment_fund_depository_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (investment_fund_category_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (investment_fund_minimum_subscription_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (investment_fund_minimum_maintenance_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (investment_fund_cut_off_time_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (nav_communication_term_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (investment_fund_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (commodity_derivative_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (double_volume_cap_reached_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (adt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (base_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (further_sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (adnt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (price_tick_rule_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (underlying_symbol_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (underlying_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (underlying_currency_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (minimum_display_qty_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (retail_service_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (self_match_prevention_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; security_name := security_name_value; net_asset_value_identifier := net_asset_value_identifier_value; security_sub_type := security_sub_type_value; maturity_month_year := maturity_month_year_value; security_status := security_status_value; strike_price := strike_price_value; strike_value := strike_value_value; exercise_style := exercise_style_value; put_or_call := put_or_call_value; position_limit := position_limit_value; nt_position_limit := nt_position_limit_value; issuer := issuer_value; cp_reg_type := cp_reg_type_value; barrier := barrier_value; last_trading_day := last_trading_day_value; automatic_expiration := automatic_expiration_value; fee_type := fee_type_value; barrier_2 := barrier_2_value; trigger_barrier := trigger_barrier_value; trigger_upper_barrier := trigger_upper_barrier_value; average_quarterly_turnover := average_quarterly_turnover_value; trading_scope := trading_scope_value; sicav_counterparty_member := sicav_counterparty_member_value; net_asset_value_indicator := net_asset_value_indicator_value; reference_trading_venue := reference_trading_venue_value; outstanding_capital := outstanding_capital_value; first_trading_date := first_trading_date_value; settlement_system := settlement_system_value; number_of_decimals := number_of_decimals_value; number_of_holders := number_of_holders_value; outstanding_shares := outstanding_shares_value; minimum_authorized_shares := minimum_authorized_shares_value; minimum_capital := minimum_capital_value; last_admission_date := last_admission_date_value; barrier_return := barrier_return_value; investment_fund_manager := investment_fund_manager_value; effective_amount_filters_routed_orders := effective_amount_filters_routed_orders_value; order_number_of_decimals := order_number_of_decimals_value; investment_fund_class := investment_fund_class_value; master_fund_name := master_fund_name_value; investment_fund_management_company := investment_fund_management_company_value; investment_fund_depository := investment_fund_depository_value; investment_fund_category := investment_fund_category_value; investment_fund_minimum_subscription_amount := investment_fund_minimum_subscription_amount_value; investment_fund_minimum_maintenance_amount := investment_fund_minimum_maintenance_amount_value; investment_fund_cut_off_time := investment_fund_cut_off_time_value; nav_communication_term := nav_communication_term_value; investment_fund_number_of_decimals := investment_fund_number_of_decimals_value; commodity_derivative_indicator := commodity_derivative_indicator_value; double_volume_cap_reached := double_volume_cap_reached_value; adt := adt_value; base_product := base_product_value; sub_product := sub_product_value; further_sub_product := further_sub_product_value; adnt := adnt_value; price_tick_rule := price_tick_rule_value; underlying_symbol := underlying_symbol_value; underlying_isin := underlying_isin_value; underlying_currency := underlying_currency_value; minimum_display_qty := minimum_display_qty_value; retail_service_flag := retail_service_flag_value; self_match_prevention := self_match_prevention_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 976.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 bound_87]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_uint by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_uint by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_uint by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_uint by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_uint by exact bound_76.
      rewrite decode_encode_bytes by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_uint by exact bound_80.
      rewrite decode_encode_uint by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_bytes by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_uint by exact bound_86.
      rewrite decode_encode_uint by exact bound_87.
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
      static_price : N;
      dynamic_price_oscilation_percentage : N;
      dynamic_range_multiplier : N;
      auction_trigger_price : N;
      auction_end_time : N;
      liquidative_value_date : N;
      bonus_warrants_with_active_bonus : N;
      security_trading_status : N;
      auction_origin : N;
      non_availability_reason : N;
      exemption_situation : list byte;
      block_oscilation_percentage : N;
      high_limit_price : N;
      low_limit_price : N;
      liquidative_value : N;
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
      (static_price record < 256 ^ N.of_nat 8)%N /\
      (dynamic_price_oscilation_percentage record < 256 ^ N.of_nat 8)%N /\
      (dynamic_range_multiplier record < 256 ^ N.of_nat 1)%N /\
      (auction_trigger_price record < 256 ^ N.of_nat 8)%N /\
      (auction_end_time record < 256 ^ N.of_nat 8)%N /\
      (liquidative_value_date record < 256 ^ N.of_nat 4)%N /\
      (bonus_warrants_with_active_bonus record < 256 ^ N.of_nat 1)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (auction_origin record < 256 ^ N.of_nat 1)%N /\
      (non_availability_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exemption_situation record) = 1 /\
      (block_oscilation_percentage record < 256 ^ N.of_nat 8)%N /\
      (high_limit_price record < 256 ^ N.of_nat 8)%N /\
      (low_limit_price record < 256 ^ N.of_nat 8)%N /\
      (liquidative_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (static_range_type record) = 1 /\
      (order_static_range record < 256 ^ N.of_nat 8)%N /\
      (block_static_range record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (static_price record) ++
      encode_uint 8 (dynamic_price_oscilation_percentage record) ++
      encode_uint 1 (dynamic_range_multiplier record) ++
      encode_uint 8 (auction_trigger_price record) ++
      encode_uint 8 (auction_end_time record) ++
      encode_uint 4 (liquidative_value_date record) ++
      encode_uint 1 (bonus_warrants_with_active_bonus record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 1 (auction_origin record) ++
      encode_uint 1 (non_availability_reason record) ++
      encode_bytes 1 (exemption_situation record) ++
      encode_uint 8 (block_oscilation_percentage record) ++
      encode_uint 8 (high_limit_price record) ++
      encode_uint 8 (low_limit_price record) ++
      encode_uint 8 (liquidative_value record) ++
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
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (static_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (dynamic_price_oscilation_percentage_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (dynamic_range_multiplier_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (auction_trigger_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (auction_end_time_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (liquidative_value_date_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (bonus_warrants_with_active_bonus_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (security_trading_status_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (auction_origin_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (non_availability_reason_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exemption_situation_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (block_oscilation_percentage_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (high_limit_price_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (low_limit_price_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (liquidative_value_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (static_range_type_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (order_static_range_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (block_static_range_value, bytes) =>
                                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; reference_price := reference_price_value; static_price := static_price_value; dynamic_price_oscilation_percentage := dynamic_price_oscilation_percentage_value; dynamic_range_multiplier := dynamic_range_multiplier_value; auction_trigger_price := auction_trigger_price_value; auction_end_time := auction_end_time_value; liquidative_value_date := liquidative_value_date_value; bonus_warrants_with_active_bonus := bonus_warrants_with_active_bonus_value; security_trading_status := security_trading_status_value; auction_origin := auction_origin_value; non_availability_reason := non_availability_reason_value; exemption_situation := exemption_situation_value; block_oscilation_percentage := block_oscilation_percentage_value; high_limit_price := high_limit_price_value; low_limit_price := low_limit_price_value; liquidative_value := liquidative_value_value; static_range_type := static_range_type_value; order_static_range := order_static_range_value; block_static_range := block_static_range_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 115.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityStatusMessage.

  Module OrderCancellationMarketMemberMessage.

    (** Used by the Server to communicate information order cancellation. The same message is used in Full-Depth data feeds (for order cancellations of any user), in the Order Entry Server (for cancellations of user orders) and in the Market & Order Server (for order cancellations of any user) *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      secondary_order_id : N;
      entry_date : N;
      retail_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (retail_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 1 (retail_flag record).

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
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (retail_flag_value, bytes) =>
                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; retail_flag := retail_flag_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End OrderCancellationMarketMemberMessage.

  Module QuoteCancellationMarketMemberMessage.

    (** Used by the Server to communicate information about quote cancellation. The same message is used in Full-Depth data feeds (for quote cancellations of any user), in the Order Entry Server (for cancellations of user quotes) and in the Market & Order Server (for quote cancellations of any user) *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      secondary_order_id : N;
      secondary_order_id_2 : N;
      retail_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (retail_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (secondary_order_id_2 record) ++
      encode_uint 1 (retail_flag record).

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
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (retail_flag_value, bytes) =>
                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; secondary_order_id_2 := secondary_order_id_2_value; retail_flag := retail_flag_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End QuoteCancellationMarketMemberMessage.

  Module OrderAndQuoteClientDataMessage.

    (** Sent by the client to set default attributes for subsequent orders and quotes. Please note that in Fixed Income it is possible to enter orders on behalf of other members (AccountMember), based on the corresponding brokerage permissions *)
    Record t := {
      request_id : N;
      client_data_id : N;
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      give_in_member : list byte;
      firm_mnemonic : list byte;
      alloc_text : list byte;
      last_capacity : list byte;
      self_match_prevention_id : N;
      automatic_order_filter_flag : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      account_type : list byte;
      self_match_prevention_type : list byte;
      client_data_reference : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member record) = 4 /\
      Datatypes.length (firm_mnemonic record) = 10 /\
      Datatypes.length (alloc_text record) = 18 /\
      Datatypes.length (last_capacity record) = 1 /\
      (self_match_prevention_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (self_match_prevention_type record) = 1 /\
      Datatypes.length (client_data_reference record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (give_in_member record) ++
      encode_bytes 10 (firm_mnemonic record) ++
      encode_bytes 18 (alloc_text record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_uint 2 (self_match_prevention_id record) ++
      encode_bytes 1 (automatic_order_filter_flag record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (self_match_prevention_type record) ++
      encode_bytes 15 (client_data_reference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (client_data_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (algorithmic_trade_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (client_id_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (account_bolsa_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (account_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (dea_flag_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (decisor_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (executor_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (liquidity_provision_activity_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (give_in_member_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (firm_mnemonic_value, bytes) =>
                                                      match decode_bytes 18 bytes with
                                                      | None => None
                                                      | Some (alloc_text_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (last_capacity_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (self_match_prevention_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (automatic_order_filter_flag_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (received_dept_id_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (persistence_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (account_type_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (self_match_prevention_type_value, bytes) =>
                                                                                      match decode_bytes 15 bytes with
                                                                                      | None => None
                                                                                      | Some (client_data_reference_value, bytes) =>
                                                                                          Some ({| request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; give_in_member := give_in_member_value; firm_mnemonic := firm_mnemonic_value; alloc_text := alloc_text_value; last_capacity := last_capacity_value; self_match_prevention_id := self_match_prevention_id_value; automatic_order_filter_flag := automatic_order_filter_flag_value; received_dept_id := received_dept_id_value; persistence := persistence_value; account_type := account_type_value; self_match_prevention_type := self_match_prevention_type_value; client_data_reference := client_data_reference_value |}, bytes)
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 97.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAndQuoteClientDataMessage.

  Module SimpleNewOrderMessage.

    (** Message sent by the client to enter a new order *)
    Record t := {
      request_id : N;
      security_code : N;
      client_data_id : N;
      order_id : N;
      side : list byte;
      price : N;
      order_qty : N;
      time_in_force : list byte;
      order_placement : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      (order_placement record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 1 (order_placement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (client_data_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (order_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (time_in_force_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_placement_value, bytes) =>
                                          Some ({| request_id := request_id_value; security_code := security_code_value; client_data_id := client_data_id_value; order_id := order_id_value; side := side_value; price := price_value; order_qty := order_qty_value; time_in_force := time_in_force_value; order_placement := order_placement_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleNewOrderMessage.

  Module SimpleNewOrderWithClientDataMessage.

    (** Message sent by the client to enter a new order and, at the same time, the values for the Client Data parmeters. Note that no ClientDataID may be assigned *)
    Record t := {
      request_id : N;
      security_code : N;
      order_id : N;
      side : list byte;
      price : N;
      order_qty : N;
      time_in_force : list byte;
      order_placement : N;
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      give_in_member : list byte;
      firm_mnemonic : list byte;
      alloc_text : list byte;
      last_capacity : list byte;
      self_match_prevention_id : N;
      automatic_order_filter_flag : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      account_type : list byte;
      self_match_prevention_type : list byte;
      client_data_reference : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time_in_force record) = 1 /\
      (order_placement record < 256 ^ N.of_nat 1)%N /\
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member record) = 4 /\
      Datatypes.length (firm_mnemonic record) = 10 /\
      Datatypes.length (alloc_text record) = 18 /\
      Datatypes.length (last_capacity record) = 1 /\
      (self_match_prevention_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (self_match_prevention_type record) = 1 /\
      Datatypes.length (client_data_reference record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 1 (order_placement record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (give_in_member record) ++
      encode_bytes 10 (firm_mnemonic record) ++
      encode_bytes 18 (alloc_text record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_uint 2 (self_match_prevention_id record) ++
      encode_bytes 1 (automatic_order_filter_flag record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (self_match_prevention_type record) ++
      encode_bytes 15 (client_data_reference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (time_in_force_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (order_placement_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (algorithmic_trade_indicator_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (client_id_value, bytes) =>
                                              match decode_bytes 16 bytes with
                                              | None => None
                                              | Some (account_bolsa_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (account_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (dea_flag_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (decisor_id_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (executor_id_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (liquidity_provision_activity_value, bytes) =>
                                                                      match decode_bytes 4 bytes with
                                                                      | None => None
                                                                      | Some (give_in_member_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (firm_mnemonic_value, bytes) =>
                                                                              match decode_bytes 18 bytes with
                                                                              | None => None
                                                                              | Some (alloc_text_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (last_capacity_value, bytes) =>
                                                                                      match decode_uint 2 bytes with
                                                                                      | None => None
                                                                                      | Some (self_match_prevention_id_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (automatic_order_filter_flag_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (received_dept_id_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (persistence_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (account_type_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (self_match_prevention_type_value, bytes) =>
                                                                                                              match decode_bytes 15 bytes with
                                                                                                              | None => None
                                                                                                              | Some (client_data_reference_value, bytes) =>
                                                                                                                  Some ({| request_id := request_id_value; security_code := security_code_value; order_id := order_id_value; side := side_value; price := price_value; order_qty := order_qty_value; time_in_force := time_in_force_value; order_placement := order_placement_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; give_in_member := give_in_member_value; firm_mnemonic := firm_mnemonic_value; alloc_text := alloc_text_value; last_capacity := last_capacity_value; self_match_prevention_id := self_match_prevention_id_value; automatic_order_filter_flag := automatic_order_filter_flag_value; received_dept_id := received_dept_id_value; persistence := persistence_value; account_type := account_type_value; self_match_prevention_type := self_match_prevention_type_value; client_data_reference := client_data_reference_value |}, bytes)
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 118.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleNewOrderWithClientDataMessage.

  Module SimpleOrderModificationMessage.

    (** Message sent by the client to modify an order. The field OrderID must contain the client reference of the order that is to be modified *)
    Record t := {
      request_id : N;
      security_code : N;
      order_id : N;
      side : list byte;
      price : N;
      order_qty : N;
      client_data_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 2 (client_data_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_qty_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (client_data_id_value, bytes) =>
                                  Some ({| request_id := request_id_value; security_code := security_code_value; order_id := order_id_value; side := side_value; price := price_value; order_qty := order_qty_value; client_data_id := client_data_id_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleOrderModificationMessage.

  Module SimpleOrderModificationWithClientDataMessage.

    (** Message sent by the client to modify an order. The field OrderID must contain the client reference of the order that is to be modified *)
    Record t := {
      request_id : N;
      security_code : N;
      order_id : N;
      side : list byte;
      price : N;
      order_qty : N;
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      give_in_member : list byte;
      firm_mnemonic : list byte;
      alloc_text : list byte;
      last_capacity : list byte;
      self_match_prevention_id : N;
      automatic_order_filter_flag : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      account_type : list byte;
      self_match_prevention_type : list byte;
      client_data_reference : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member record) = 4 /\
      Datatypes.length (firm_mnemonic record) = 10 /\
      Datatypes.length (alloc_text record) = 18 /\
      Datatypes.length (last_capacity record) = 1 /\
      (self_match_prevention_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (self_match_prevention_type record) = 1 /\
      Datatypes.length (client_data_reference record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (give_in_member record) ++
      encode_bytes 10 (firm_mnemonic record) ++
      encode_bytes 18 (alloc_text record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_uint 2 (self_match_prevention_id record) ++
      encode_bytes 1 (automatic_order_filter_flag record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (self_match_prevention_type record) ++
      encode_bytes 15 (client_data_reference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_qty_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (algorithmic_trade_indicator_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (client_id_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (account_bolsa_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (account_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (dea_flag_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (decisor_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (executor_id_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (liquidity_provision_activity_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (give_in_member_value, bytes) =>
                                                                  match decode_bytes 10 bytes with
                                                                  | None => None
                                                                  | Some (firm_mnemonic_value, bytes) =>
                                                                      match decode_bytes 18 bytes with
                                                                      | None => None
                                                                      | Some (alloc_text_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (last_capacity_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (self_match_prevention_id_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (automatic_order_filter_flag_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (received_dept_id_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (persistence_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (account_type_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (self_match_prevention_type_value, bytes) =>
                                                                                                      match decode_bytes 15 bytes with
                                                                                                      | None => None
                                                                                                      | Some (client_data_reference_value, bytes) =>
                                                                                                          Some ({| request_id := request_id_value; security_code := security_code_value; order_id := order_id_value; side := side_value; price := price_value; order_qty := order_qty_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; give_in_member := give_in_member_value; firm_mnemonic := firm_mnemonic_value; alloc_text := alloc_text_value; last_capacity := last_capacity_value; self_match_prevention_id := self_match_prevention_id_value; automatic_order_filter_flag := automatic_order_filter_flag_value; received_dept_id := received_dept_id_value; persistence := persistence_value; account_type := account_type_value; self_match_prevention_type := self_match_prevention_type_value; client_data_reference := client_data_reference_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 116.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleOrderModificationWithClientDataMessage.

  Module OrderCancellationRequestMessage.

    (** Message sent by the client to cancel an order. The field OrderID must contain a reference to the order that is to be cancelled *)
    Record t := {
      request_id : N;
      security_code : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 4 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  Some ({| request_id := request_id_value; security_code := security_code_value; order_id := order_id_value |}, bytes)
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

  End OrderCancellationRequestMessage.

  Module NewQuoteMessage.

    (** Message sent by the client application to create a new quote. A new quote by the same user on the same SecurityCode and with the same ClientDataID cancels the previous one *)
    Record t := {
      request_id : N;
      security_code : N;
      client_data_id : N;
      bid_size_1 : N;
      bid_px_1 : N;
      ask_size_1 : N;
      ask_px_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (bid_size_1 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (ask_size_1 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 4 (bid_size_1 record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 4 (ask_size_1 record) ++
      encode_uint 8 (ask_px_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (client_data_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (bid_size_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (bid_px_1_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ask_size_1_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ask_px_1_value, bytes) =>
                                  Some ({| request_id := request_id_value; security_code := security_code_value; client_data_id := client_data_id_value; bid_size_1 := bid_size_1_value; bid_px_1 := bid_px_1_value; ask_size_1 := ask_size_1_value; ask_px_1 := ask_px_1_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NewQuoteMessage.

  Module QuoteModificationRequestMessage.

    (** Message sent by the client to modify a quote. Field ClientDataID is required in RF to identify a quote *)
    Record t := {
      request_id : N;
      security_code : N;
      client_data_id : N;
      bid_px_1 : N;
      ask_px_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 8 (ask_px_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (client_data_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_px_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (ask_px_1_value, bytes) =>
                          Some ({| request_id := request_id_value; security_code := security_code_value; client_data_id := client_data_id_value; bid_px_1 := bid_px_1_value; ask_px_1 := ask_px_1_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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

  End QuoteModificationRequestMessage.

  Module QuoteCancellationRequestMessage.

    (** Message sent by the client to cancel a quote *)
    Record t := {
      request_id : N;
      security_code : N;
      client_data_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 2 (client_data_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (client_data_id_value, bytes) =>
                  Some ({| request_id := request_id_value; security_code := security_code_value; client_data_id := client_data_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End QuoteCancellationRequestMessage.

  Module MassOrderquoteCancellationMessage.

    (** Message sent by the client to request the cancellation of multiple orders and or quotes, based on the specified selection criteria *)
    Record t := {
      request_id : N;
      security_code : N;
      side : list byte;
      issuer : list byte;
      account_bolsa : list byte;
      order_or_quote_cancel : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (issuer record) = 12 /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (order_or_quote_cancel record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 12 (issuer record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 1 (order_or_quote_cancel record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (issuer_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (account_bolsa_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (order_or_quote_cancel_value, bytes) =>
                              Some ({| request_id := request_id_value; security_code := security_code_value; side := side_value; issuer := issuer_value; account_bolsa := account_bolsa_value; order_or_quote_cancel := order_or_quote_cancel_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassOrderquoteCancellationMessage.

  Module OrderAndQuoteClientDataParametersAckNackMessage.

    (** Sent by the server to confirm an Order and Quote Client Data Parameters message *)
    Record t := {
      sequence_number : N;
      request_id : N;
      status : N;
      client_data_id : N;
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      give_in_member : list byte;
      firm_mnemonic : list byte;
      alloc_text : list byte;
      last_capacity : list byte;
      self_match_prevention_id : N;
      automatic_order_filter_flag : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      account_type : list byte;
      self_match_prevention_type : list byte;
      client_data_reference : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (status record < 256 ^ N.of_nat 1)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member record) = 4 /\
      Datatypes.length (firm_mnemonic record) = 10 /\
      Datatypes.length (alloc_text record) = 18 /\
      Datatypes.length (last_capacity record) = 1 /\
      (self_match_prevention_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (self_match_prevention_type record) = 1 /\
      Datatypes.length (client_data_reference record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 1 (status record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (give_in_member record) ++
      encode_bytes 10 (firm_mnemonic record) ++
      encode_bytes 18 (alloc_text record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_uint 2 (self_match_prevention_id record) ++
      encode_bytes 1 (automatic_order_filter_flag record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (self_match_prevention_type record) ++
      encode_bytes 15 (client_data_reference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (request_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (client_data_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (algorithmic_trade_indicator_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (client_id_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (account_bolsa_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (account_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (dea_flag_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (decisor_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (executor_id_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (liquidity_provision_activity_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (give_in_member_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (firm_mnemonic_value, bytes) =>
                                                              match decode_bytes 18 bytes with
                                                              | None => None
                                                              | Some (alloc_text_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (last_capacity_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (self_match_prevention_id_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (automatic_order_filter_flag_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (received_dept_id_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (persistence_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (account_type_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (self_match_prevention_type_value, bytes) =>
                                                                                              match decode_bytes 15 bytes with
                                                                                              | None => None
                                                                                              | Some (client_data_reference_value, bytes) =>
                                                                                                  Some ({| sequence_number := sequence_number_value; request_id := request_id_value; status := status_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; give_in_member := give_in_member_value; firm_mnemonic := firm_mnemonic_value; alloc_text := alloc_text_value; last_capacity := last_capacity_value; self_match_prevention_id := self_match_prevention_id_value; automatic_order_filter_flag := automatic_order_filter_flag_value; received_dept_id := received_dept_id_value; persistence := persistence_value; account_type := account_type_value; self_match_prevention_type := self_match_prevention_type_value; client_data_reference := client_data_reference_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAndQuoteClientDataParametersAckNackMessage.

  Module SimpleOrderStatusMessage.

    (** Sent by the server to inform about the order status. Please note that the first fields of this message are the same as the ones for Order Market Pre- Transparency Information (Msg Type = 0x03) (see section 5.4.12) *)
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
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ord_rej_reason : list byte;
      exec_type : list byte;
      request_id : N;
      client_data_id : N;
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
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ord_rej_reason record) = 1 /\
      Datatypes.length (exec_type record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N.

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
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ord_rej_reason record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record).

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
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (order_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (secondary_exec_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (order_qty_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (ord_status_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (ord_rej_reason_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exec_type_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (request_id_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (client_data_id_value, bytes) =>
                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; side := side_value; priority := priority_value; price := price_value; display_qty := display_qty_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; exec_type := exec_type_value; request_id := request_id_value; client_data_id := client_data_id_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleOrderStatusMessage.

  Module QuoteStatusMessage.

    (** Sent by the server to inform about the status of a Quote *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      secondary_order_id : N;
      secondary_order_id_2 : N;
      priority : N;
      price : N;
      display_qty : N;
      priority_2 : N;
      price_2 : N;
      display_qty_2 : N;
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ord_rej_reason : list byte;
      exec_type : list byte;
      order_id_2 : N;
      secondary_exec_id_2 : N;
      order_qty_2 : N;
      ord_status_2 : list byte;
      ord_rej_reason_2 : list byte;
      exec_type_2 : list byte;
      request_id : N;
      client_data_id : N;
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
      (priority_2 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 8)%N /\
      (display_qty_2 record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ord_rej_reason record) = 1 /\
      Datatypes.length (exec_type record) = 1 /\
      (order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id_2 record < 256 ^ N.of_nat 4)%N /\
      (order_qty_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status_2 record) = 1 /\
      Datatypes.length (ord_rej_reason_2 record) = 1 /\
      Datatypes.length (exec_type_2 record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (secondary_order_id_2 record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 4 (priority_2 record) ++
      encode_uint 8 (price_2 record) ++
      encode_uint 4 (display_qty_2 record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ord_rej_reason record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 4 (order_id_2 record) ++
      encode_uint 4 (secondary_exec_id_2 record) ++
      encode_uint 4 (order_qty_2 record) ++
      encode_bytes 1 (ord_status_2 record) ++
      encode_bytes 1 (ord_rej_reason_2 record) ++
      encode_bytes 1 (exec_type_2 record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record).

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
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (priority_2_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (price_2_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (display_qty_2_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (order_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (secondary_exec_id_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (order_qty_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (ord_status_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ord_rej_reason_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (exec_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (order_id_2_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (secondary_exec_id_2_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (order_qty_2_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (ord_status_2_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (ord_rej_reason_2_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (exec_type_2_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (request_id_value, bytes) =>
                                                                                                      match decode_uint 2 bytes with
                                                                                                      | None => None
                                                                                                      | Some (client_data_id_value, bytes) =>
                                                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; secondary_order_id_2 := secondary_order_id_2_value; priority := priority_value; price := price_value; display_qty := display_qty_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; exec_type := exec_type_value; order_id_2 := order_id_2_value; secondary_exec_id_2 := secondary_exec_id_2_value; order_qty_2 := order_qty_2_value; ord_status_2 := ord_status_2_value; ord_rej_reason_2 := ord_rej_reason_2_value; exec_type_2 := exec_type_2_value; request_id := request_id_value; client_data_id := client_data_id_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteStatusMessage.

  Module OrderCancelRejectMessage.

    (** Sent by the server to inform about the rejection of a Simple order modification (MsgType = 0x47) or an Order cancellation request (MsgType = 0x46) *)
    Record t := {
      sequence_number : N;
      transaction_date_and_time : N;
      order_id : N;
      ord_status : list byte;
      cxl_rej_response_to : list byte;
      cxl_rej_reason : list byte;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (cxl_rej_response_to record) = 1 /\
      Datatypes.length (cxl_rej_reason record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (cxl_rej_response_to record) ++
      encode_bytes 1 (cxl_rej_reason record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_date_and_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (ord_status_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cxl_rej_response_to_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cxl_rej_reason_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (request_id_value, bytes) =>
                                  Some ({| sequence_number := sequence_number_value; transaction_date_and_time := transaction_date_and_time_value; order_id := order_id_value; ord_status := ord_status_value; cxl_rej_response_to := cxl_rej_response_to_value; cxl_rej_reason := cxl_rej_reason_value; request_id := request_id_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelRejectMessage.

  Module MassOrderquoteCancellationCompletionMessage.

    (** Message reporting the completion of a valid mass order cancellation request. More than one message may be sent for a single RequestID *)
    Record t := {
      sequence_number : N;
      transaction_date_and_time : N;
      trading_unit : N;
      order_or_quote_cancel : list byte;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trading_unit record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (order_or_quote_cancel record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 1 (trading_unit record) ++
      encode_bytes 1 (order_or_quote_cancel record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_date_and_time_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_unit_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_or_quote_cancel_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (request_id_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; transaction_date_and_time := transaction_date_and_time_value; trading_unit := trading_unit_value; order_or_quote_cancel := order_or_quote_cancel_value; request_id := request_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassOrderquoteCancellationCompletionMessage.

  Module MassOrderquoteCancellationRejectMessage.

    (** Message reporting the rejection of a mass order cancellation request. More than one message may be sent for a single RequestID *)
    Record t := {
      sequence_number : N;
      transaction_date_and_time : N;
      trading_unit : N;
      mass_cancel_reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trading_unit record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mass_cancel_reject_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 1 (trading_unit record) ++
      encode_bytes 1 (mass_cancel_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_date_and_time_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_unit_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (mass_cancel_reject_reason_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; transaction_date_and_time := transaction_date_and_time_value; trading_unit := trading_unit_value; mass_cancel_reject_reason := mass_cancel_reject_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassOrderquoteCancellationRejectMessage.

  Module BusinessMessageRejectMessage.

    (** It may be sent by the server to inform about the rejection of a supported message that is syntactically correct in an unsupported situation *)
    Record t := {
      sequence_number : N;
      transaction_date_and_time : N;
      ref_msg_type : N;
      business_reject_reason : N;
      text_c_65 : list byte;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (ref_msg_type record < 256 ^ N.of_nat 1)%N /\
      (business_reject_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (text_c_65 record) = 65 /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 1 (ref_msg_type record) ++
      encode_uint 1 (business_reject_reason record) ++
      encode_bytes 65 (text_c_65 record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transaction_date_and_time_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (ref_msg_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (business_reject_reason_value, bytes) =>
                      match decode_bytes 65 bytes with
                      | None => None
                      | Some (text_c_65_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (request_id_value, bytes) =>
                              Some ({| sequence_number := sequence_number_value; transaction_date_and_time := transaction_date_and_time_value; ref_msg_type := ref_msg_type_value; business_reject_reason := business_reject_reason_value; text_c_65 := text_c_65_value; request_id := request_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BusinessMessageRejectMessage.

  Module ExecutionPrivateInformation2LegsMessage.

    (** Sent by the server to inform about a trade where two orders of the user are involved both as Buyer and Seller *)
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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ccp_code : list byte;
      aggressor_indicator : list byte;
      request_id : N;
      client_data_id : N;
      secondary_order_id_2 : N;
      entry_date_2 : N;
      priority_2 : N;
      price_2 : N;
      display_qty_2 : N;
      order_id_2 : N;
      secondary_exec_id_2 : N;
      order_qty_2 : N;
      ord_status_2 : list byte;
      ccp_code_2 : list byte;
      aggressor_indicator_2 : list byte;
      request_id_2 : N;
      client_data_id_2 : N;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ccp_code record) = 1 /\
      Datatypes.length (aggressor_indicator record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (secondary_order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (entry_date_2 record < 256 ^ N.of_nat 4)%N /\
      (priority_2 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 8)%N /\
      (display_qty_2 record < 256 ^ N.of_nat 4)%N /\
      (order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id_2 record < 256 ^ N.of_nat 4)%N /\
      (order_qty_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status_2 record) = 1 /\
      Datatypes.length (ccp_code_2 record) = 1 /\
      Datatypes.length (aggressor_indicator_2 record) = 1 /\
      (request_id_2 record < 256 ^ N.of_nat 4)%N /\
      (client_data_id_2 record < 256 ^ N.of_nat 2)%N.

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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ccp_code record) ++
      encode_bytes 1 (aggressor_indicator record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 4 (secondary_order_id_2 record) ++
      encode_uint 4 (entry_date_2 record) ++
      encode_uint 4 (priority_2 record) ++
      encode_uint 8 (price_2 record) ++
      encode_uint 4 (display_qty_2 record) ++
      encode_uint 4 (order_id_2 record) ++
      encode_uint 4 (secondary_exec_id_2 record) ++
      encode_uint 4 (order_qty_2 record) ++
      encode_bytes 1 (ord_status_2 record) ++
      encode_bytes 1 (ccp_code_2 record) ++
      encode_bytes 1 (aggressor_indicator_2 record) ++
      encode_uint 4 (request_id_2 record) ++
      encode_uint 2 (client_data_id_2 record).

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
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (buyer_bolsa_code_value, bytes) =>
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
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (order_id_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (secondary_exec_id_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (order_qty_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ord_status_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ccp_code_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (aggressor_indicator_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (request_id_value, bytes) =>
                                                                                                                      match decode_uint 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (client_data_id_value, bytes) =>
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
                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (order_id_2_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (secondary_exec_id_2_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (order_qty_2_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ord_status_2_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ccp_code_2_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (aggressor_indicator_2_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (request_id_2_value, bytes) =>
                                                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (client_data_id_2_value, bytes) =>
                                                                                                                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; secondary_order_id_2 := secondary_order_id_2_value; entry_date_2 := entry_date_2_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; order_id_2 := order_id_2_value; secondary_exec_id_2 := secondary_exec_id_2_value; order_qty_2 := order_qty_2_value; ord_status_2 := ord_status_2_value; ccp_code_2 := ccp_code_2_value; aggressor_indicator_2 := aggressor_indicator_2_value; request_id_2 := request_id_2_value; client_data_id_2 := client_data_id_2_value |}, bytes)
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 145.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 bound_41]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
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
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionPrivateInformation2LegsMessage.

  Module TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.

    (** Sent by the server to inform about a trade produced due to any reason other than order matching, also to inform about trades produced due to order matching in a Dark pool. The user is involved in the trade as Buyer. It is also sent to inform about the amendment or cancellation of whatever origin trade where the user is involved as Buyer. Shares the same layout as the next message *)
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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
      last_change_flag : N;
      benc_rfpt_flag : list byte;
      trade_price_condition : list byte;
      pre_trade_transparency_waiver : list byte;
      deferral_waiver : list byte;
      publish_date_and_time : N;
      trade_date : N;
      trade_session_date : N;
      volume_float : N;
      sicav_fund_counterparty_side : list byte;
      amended_trade_type : list byte;
      exec_ref_id : N;
      amended_trade_date : N;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ccp_code : list byte;
      aggressor_indicator : list byte;
      request_id : N;
      client_data_id : N;
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      give_in_member : list byte;
      firm_mnemonic : list byte;
      alloc_text : list byte;
      last_capacity : list byte;
      self_match_prevention_id : N;
      automatic_order_filter_flag : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      account_type : list byte;
      self_match_prevention_type : list byte;
      member : list byte;
      trader : list byte;
      sub_member : list byte;
      cross_id : N;
      bolsa_code : list byte;
      csdbic : list byte;
      participant : list byte;
      cta_liq : list byte;
      ccv : list byte;
      order_security_code : N;
      external_member : list byte;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (last_change_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benc_rfpt_flag record) = 1 /\
      Datatypes.length (trade_price_condition record) = 1 /\
      Datatypes.length (pre_trade_transparency_waiver record) = 1 /\
      Datatypes.length (deferral_waiver record) = 1 /\
      (publish_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (trade_session_date record < 256 ^ N.of_nat 4)%N /\
      (volume_float record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sicav_fund_counterparty_side record) = 1 /\
      Datatypes.length (amended_trade_type record) = 1 /\
      (exec_ref_id record < 256 ^ N.of_nat 4)%N /\
      (amended_trade_date record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ccp_code record) = 1 /\
      Datatypes.length (aggressor_indicator record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member record) = 4 /\
      Datatypes.length (firm_mnemonic record) = 10 /\
      Datatypes.length (alloc_text record) = 18 /\
      Datatypes.length (last_capacity record) = 1 /\
      (self_match_prevention_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (self_match_prevention_type record) = 1 /\
      Datatypes.length (member record) = 4 /\
      Datatypes.length (trader record) = 3 /\
      Datatypes.length (sub_member record) = 1 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bolsa_code record) = 1 /\
      Datatypes.length (csdbic record) = 11 /\
      Datatypes.length (participant record) = 11 /\
      Datatypes.length (cta_liq record) = 35 /\
      Datatypes.length (ccv record) = 20 /\
      (order_security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (external_member record) = 4.

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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 1 (last_change_flag record) ++
      encode_bytes 1 (benc_rfpt_flag record) ++
      encode_bytes 1 (trade_price_condition record) ++
      encode_bytes 1 (pre_trade_transparency_waiver record) ++
      encode_bytes 1 (deferral_waiver record) ++
      encode_uint 8 (publish_date_and_time record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 4 (trade_session_date record) ++
      encode_uint 8 (volume_float record) ++
      encode_bytes 1 (sicav_fund_counterparty_side record) ++
      encode_bytes 1 (amended_trade_type record) ++
      encode_uint 4 (exec_ref_id record) ++
      encode_uint 4 (amended_trade_date record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ccp_code record) ++
      encode_bytes 1 (aggressor_indicator record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (give_in_member record) ++
      encode_bytes 10 (firm_mnemonic record) ++
      encode_bytes 18 (alloc_text record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_uint 2 (self_match_prevention_id record) ++
      encode_bytes 1 (automatic_order_filter_flag record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (self_match_prevention_type record) ++
      encode_bytes 4 (member record) ++
      encode_bytes 3 (trader record) ++
      encode_bytes 1 (sub_member record) ++
      encode_uint 4 (cross_id record) ++
      encode_bytes 1 (bolsa_code record) ++
      encode_bytes 11 (csdbic record) ++
      encode_bytes 11 (participant record) ++
      encode_bytes 35 (cta_liq record) ++
      encode_bytes 20 (ccv record) ++
      encode_uint 4 (order_security_code record) ++
      encode_bytes 4 (external_member record).

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
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (buyer_bolsa_code_value, bytes) =>
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
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (publish_date_and_time_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (trade_date_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_session_date_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (volume_float_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (sicav_fund_counterparty_side_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (amended_trade_type_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (exec_ref_id_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (amended_trade_date_value, bytes) =>
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
                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (order_id_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (secondary_exec_id_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (order_qty_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ord_status_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ccp_code_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (aggressor_indicator_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (request_id_value, bytes) =>
                                                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (client_data_id_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (algorithmic_trade_indicator_value, bytes) =>
                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (client_id_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 16 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (account_bolsa_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (account_value, bytes) =>
                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (dea_flag_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (decisor_id_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (executor_id_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (liquidity_provision_activity_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (give_in_member_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (firm_mnemonic_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 18 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (alloc_text_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (last_capacity_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (self_match_prevention_id_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (automatic_order_filter_flag_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (received_dept_id_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (persistence_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (account_type_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (self_match_prevention_type_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (member_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (trader_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (sub_member_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (cross_id_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (bolsa_code_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (csdbic_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (participant_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 35 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (cta_liq_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (ccv_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (order_security_code_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (external_member_value, bytes) =>
                                                                                                                                                                                                                                                                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; volume_float := volume_float_value; sicav_fund_counterparty_side := sicav_fund_counterparty_side_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; give_in_member := give_in_member_value; firm_mnemonic := firm_mnemonic_value; alloc_text := alloc_text_value; last_capacity := last_capacity_value; self_match_prevention_id := self_match_prevention_id_value; automatic_order_filter_flag := automatic_order_filter_flag_value; received_dept_id := received_dept_id_value; persistence := persistence_value; account_type := account_type_value; self_match_prevention_type := self_match_prevention_type_value; member := member_value; trader := trader_value; sub_member := sub_member_value; cross_id := cross_id_value; bolsa_code := bolsa_code_value; csdbic := csdbic_value; participant := participant_value; cta_liq := cta_liq_value; ccv := ccv_value; order_security_code := order_security_code_value; external_member := external_member_value |}, bytes)
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 317.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 bound_70]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
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
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTradeAmendmentOrCancellation1LegBuyPrivateInformationMessage.

  Module TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.

    (** Sent by the server to inform about a trade produced due to any reason other than order matching, also to inform about trades produced due to order matching in a Dark pool. The user is involved in the trade as Seller *)
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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
      last_change_flag : N;
      benc_rfpt_flag : list byte;
      trade_price_condition : list byte;
      pre_trade_transparency_waiver : list byte;
      deferral_waiver : list byte;
      publish_date_and_time : N;
      trade_date : N;
      trade_session_date : N;
      volume_float : N;
      sicav_fund_counterparty_side : list byte;
      amended_trade_type : list byte;
      exec_ref_id : N;
      amended_trade_date : N;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ccp_code : list byte;
      aggressor_indicator : list byte;
      request_id : N;
      client_data_id : N;
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      give_in_member : list byte;
      firm_mnemonic : list byte;
      alloc_text : list byte;
      last_capacity : list byte;
      self_match_prevention_id : N;
      automatic_order_filter_flag : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      account_type : list byte;
      self_match_prevention_type : list byte;
      member : list byte;
      trader : list byte;
      sub_member : list byte;
      cross_id : N;
      bolsa_code : list byte;
      csdbic : list byte;
      participant : list byte;
      cta_liq : list byte;
      ccv : list byte;
      order_security_code : N;
      external_member : list byte;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (last_change_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benc_rfpt_flag record) = 1 /\
      Datatypes.length (trade_price_condition record) = 1 /\
      Datatypes.length (pre_trade_transparency_waiver record) = 1 /\
      Datatypes.length (deferral_waiver record) = 1 /\
      (publish_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (trade_session_date record < 256 ^ N.of_nat 4)%N /\
      (volume_float record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sicav_fund_counterparty_side record) = 1 /\
      Datatypes.length (amended_trade_type record) = 1 /\
      (exec_ref_id record < 256 ^ N.of_nat 4)%N /\
      (amended_trade_date record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ccp_code record) = 1 /\
      Datatypes.length (aggressor_indicator record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member record) = 4 /\
      Datatypes.length (firm_mnemonic record) = 10 /\
      Datatypes.length (alloc_text record) = 18 /\
      Datatypes.length (last_capacity record) = 1 /\
      (self_match_prevention_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (self_match_prevention_type record) = 1 /\
      Datatypes.length (member record) = 4 /\
      Datatypes.length (trader record) = 3 /\
      Datatypes.length (sub_member record) = 1 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bolsa_code record) = 1 /\
      Datatypes.length (csdbic record) = 11 /\
      Datatypes.length (participant record) = 11 /\
      Datatypes.length (cta_liq record) = 35 /\
      Datatypes.length (ccv record) = 20 /\
      (order_security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (external_member record) = 4.

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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 1 (last_change_flag record) ++
      encode_bytes 1 (benc_rfpt_flag record) ++
      encode_bytes 1 (trade_price_condition record) ++
      encode_bytes 1 (pre_trade_transparency_waiver record) ++
      encode_bytes 1 (deferral_waiver record) ++
      encode_uint 8 (publish_date_and_time record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 4 (trade_session_date record) ++
      encode_uint 8 (volume_float record) ++
      encode_bytes 1 (sicav_fund_counterparty_side record) ++
      encode_bytes 1 (amended_trade_type record) ++
      encode_uint 4 (exec_ref_id record) ++
      encode_uint 4 (amended_trade_date record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ccp_code record) ++
      encode_bytes 1 (aggressor_indicator record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (give_in_member record) ++
      encode_bytes 10 (firm_mnemonic record) ++
      encode_bytes 18 (alloc_text record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_uint 2 (self_match_prevention_id record) ++
      encode_bytes 1 (automatic_order_filter_flag record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (self_match_prevention_type record) ++
      encode_bytes 4 (member record) ++
      encode_bytes 3 (trader record) ++
      encode_bytes 1 (sub_member record) ++
      encode_uint 4 (cross_id record) ++
      encode_bytes 1 (bolsa_code record) ++
      encode_bytes 11 (csdbic record) ++
      encode_bytes 11 (participant record) ++
      encode_bytes 35 (cta_liq record) ++
      encode_bytes 20 (ccv record) ++
      encode_uint 4 (order_security_code record) ++
      encode_bytes 4 (external_member record).

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
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (buyer_bolsa_code_value, bytes) =>
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
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (publish_date_and_time_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (trade_date_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_session_date_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (volume_float_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (sicav_fund_counterparty_side_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (amended_trade_type_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (exec_ref_id_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (amended_trade_date_value, bytes) =>
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
                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (order_id_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (secondary_exec_id_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (order_qty_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ord_status_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ccp_code_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (aggressor_indicator_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (request_id_value, bytes) =>
                                                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (client_data_id_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (algorithmic_trade_indicator_value, bytes) =>
                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (client_id_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 16 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (account_bolsa_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (account_value, bytes) =>
                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (dea_flag_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (decisor_id_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (executor_id_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (liquidity_provision_activity_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (give_in_member_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (firm_mnemonic_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 18 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (alloc_text_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (last_capacity_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (self_match_prevention_id_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (automatic_order_filter_flag_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (received_dept_id_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (persistence_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (account_type_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (self_match_prevention_type_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (member_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (trader_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (sub_member_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (cross_id_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (bolsa_code_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (csdbic_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (participant_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 35 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (cta_liq_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (ccv_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (order_security_code_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (external_member_value, bytes) =>
                                                                                                                                                                                                                                                                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; volume_float := volume_float_value; sicav_fund_counterparty_side := sicav_fund_counterparty_side_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; give_in_member := give_in_member_value; firm_mnemonic := firm_mnemonic_value; alloc_text := alloc_text_value; last_capacity := last_capacity_value; self_match_prevention_id := self_match_prevention_id_value; automatic_order_filter_flag := automatic_order_filter_flag_value; received_dept_id := received_dept_id_value; persistence := persistence_value; account_type := account_type_value; self_match_prevention_type := self_match_prevention_type_value; member := member_value; trader := trader_value; sub_member := sub_member_value; cross_id := cross_id_value; bolsa_code := bolsa_code_value; csdbic := csdbic_value; participant := participant_value; cta_liq := cta_liq_value; ccv := ccv_value; order_security_code := order_security_code_value; external_member := external_member_value |}, bytes)
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 317.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 bound_70]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
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
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTradeAmendmentOrCancellation1LegSellPrivateInformationMessage.

  Module TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.

    (** Sent by the server to inform about a trade produced due to any reason other than order matching, also to inform about trades produced due to order matching in a Dark pool. The user is involved in the trade both as Buyer and Seller *)
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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
      last_change_flag : N;
      benc_rfpt_flag : list byte;
      trade_price_condition : list byte;
      pre_trade_transparency_waiver : list byte;
      deferral_waiver : list byte;
      publish_date_and_time : N;
      trade_date : N;
      trade_session_date : N;
      volume_float : N;
      sicav_fund_counterparty_side : list byte;
      amended_trade_type : list byte;
      exec_ref_id : N;
      amended_trade_date : N;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ccp_code : list byte;
      aggressor_indicator : list byte;
      request_id : N;
      client_data_id : N;
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      give_in_member : list byte;
      firm_mnemonic : list byte;
      alloc_text : list byte;
      last_capacity : list byte;
      self_match_prevention_id : N;
      automatic_order_filter_flag : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      account_type : list byte;
      self_match_prevention_type : list byte;
      member : list byte;
      trader : list byte;
      sub_member : list byte;
      cross_id : N;
      bolsa_code : list byte;
      csdbic : list byte;
      participant : list byte;
      cta_liq : list byte;
      ccv : list byte;
      order_security_code : N;
      external_member : list byte;
      secondary_order_id_2 : N;
      entry_date_2 : N;
      priority_2 : N;
      price_2 : N;
      display_qty_2 : N;
      order_id_2 : N;
      secondary_exec_id_2 : N;
      order_qty_2 : N;
      ord_status_2 : list byte;
      ccp_code_2 : list byte;
      aggressor_indicator_2 : list byte;
      request_id_2 : N;
      client_data_id_2 : N;
      algorithmic_trade_indicator_2 : N;
      client_id_2 : N;
      account_bolsa_2 : list byte;
      account_2 : list byte;
      dea_flag_2 : N;
      decisor_id_2 : N;
      executor_id_2 : N;
      liquidity_provision_activity_2 : N;
      give_in_member_2 : list byte;
      firm_mnemonic_2 : list byte;
      alloc_text_2 : list byte;
      last_capacity_2 : list byte;
      self_match_prevention_id_2 : N;
      automatic_order_filter_flag_2 : list byte;
      received_dept_id_2 : list byte;
      persistence_2 : list byte;
      account_type_2 : list byte;
      self_match_prevention_type_2 : list byte;
      member_2 : list byte;
      trader_2 : list byte;
      sub_member_2 : list byte;
      cross_id_2 : N;
      bolsa_code_2 : list byte;
      csdbic_2 : list byte;
      participant_2 : list byte;
      cta_liq_2 : list byte;
      ccv_2 : list byte;
      order_security_code_2 : N;
      external_member_2 : list byte;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (last_change_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benc_rfpt_flag record) = 1 /\
      Datatypes.length (trade_price_condition record) = 1 /\
      Datatypes.length (pre_trade_transparency_waiver record) = 1 /\
      Datatypes.length (deferral_waiver record) = 1 /\
      (publish_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (trade_session_date record < 256 ^ N.of_nat 4)%N /\
      (volume_float record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sicav_fund_counterparty_side record) = 1 /\
      Datatypes.length (amended_trade_type record) = 1 /\
      (exec_ref_id record < 256 ^ N.of_nat 4)%N /\
      (amended_trade_date record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ccp_code record) = 1 /\
      Datatypes.length (aggressor_indicator record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N /\
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member record) = 4 /\
      Datatypes.length (firm_mnemonic record) = 10 /\
      Datatypes.length (alloc_text record) = 18 /\
      Datatypes.length (last_capacity record) = 1 /\
      (self_match_prevention_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (self_match_prevention_type record) = 1 /\
      Datatypes.length (member record) = 4 /\
      Datatypes.length (trader record) = 3 /\
      Datatypes.length (sub_member record) = 1 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bolsa_code record) = 1 /\
      Datatypes.length (csdbic record) = 11 /\
      Datatypes.length (participant record) = 11 /\
      Datatypes.length (cta_liq record) = 35 /\
      Datatypes.length (ccv record) = 20 /\
      (order_security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (external_member record) = 4 /\
      (secondary_order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (entry_date_2 record < 256 ^ N.of_nat 4)%N /\
      (priority_2 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 8)%N /\
      (display_qty_2 record < 256 ^ N.of_nat 4)%N /\
      (order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id_2 record < 256 ^ N.of_nat 4)%N /\
      (order_qty_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status_2 record) = 1 /\
      Datatypes.length (ccp_code_2 record) = 1 /\
      Datatypes.length (aggressor_indicator_2 record) = 1 /\
      (request_id_2 record < 256 ^ N.of_nat 4)%N /\
      (client_data_id_2 record < 256 ^ N.of_nat 2)%N /\
      (algorithmic_trade_indicator_2 record < 256 ^ N.of_nat 1)%N /\
      (client_id_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa_2 record) = 16 /\
      Datatypes.length (account_2 record) = 5 /\
      (dea_flag_2 record < 256 ^ N.of_nat 1)%N /\
      (decisor_id_2 record < 256 ^ N.of_nat 4)%N /\
      (executor_id_2 record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (give_in_member_2 record) = 4 /\
      Datatypes.length (firm_mnemonic_2 record) = 10 /\
      Datatypes.length (alloc_text_2 record) = 18 /\
      Datatypes.length (last_capacity_2 record) = 1 /\
      (self_match_prevention_id_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (automatic_order_filter_flag_2 record) = 1 /\
      Datatypes.length (received_dept_id_2 record) = 1 /\
      Datatypes.length (persistence_2 record) = 1 /\
      Datatypes.length (account_type_2 record) = 1 /\
      Datatypes.length (self_match_prevention_type_2 record) = 1 /\
      Datatypes.length (member_2 record) = 4 /\
      Datatypes.length (trader_2 record) = 3 /\
      Datatypes.length (sub_member_2 record) = 1 /\
      (cross_id_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bolsa_code_2 record) = 1 /\
      Datatypes.length (csdbic_2 record) = 11 /\
      Datatypes.length (participant_2 record) = 11 /\
      Datatypes.length (cta_liq_2 record) = 35 /\
      Datatypes.length (ccv_2 record) = 20 /\
      (order_security_code_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (external_member_2 record) = 4.

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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 1 (last_change_flag record) ++
      encode_bytes 1 (benc_rfpt_flag record) ++
      encode_bytes 1 (trade_price_condition record) ++
      encode_bytes 1 (pre_trade_transparency_waiver record) ++
      encode_bytes 1 (deferral_waiver record) ++
      encode_uint 8 (publish_date_and_time record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 4 (trade_session_date record) ++
      encode_uint 8 (volume_float record) ++
      encode_bytes 1 (sicav_fund_counterparty_side record) ++
      encode_bytes 1 (amended_trade_type record) ++
      encode_uint 4 (exec_ref_id record) ++
      encode_uint 4 (amended_trade_date record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ccp_code record) ++
      encode_bytes 1 (aggressor_indicator record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (give_in_member record) ++
      encode_bytes 10 (firm_mnemonic record) ++
      encode_bytes 18 (alloc_text record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_uint 2 (self_match_prevention_id record) ++
      encode_bytes 1 (automatic_order_filter_flag record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (self_match_prevention_type record) ++
      encode_bytes 4 (member record) ++
      encode_bytes 3 (trader record) ++
      encode_bytes 1 (sub_member record) ++
      encode_uint 4 (cross_id record) ++
      encode_bytes 1 (bolsa_code record) ++
      encode_bytes 11 (csdbic record) ++
      encode_bytes 11 (participant record) ++
      encode_bytes 35 (cta_liq record) ++
      encode_bytes 20 (ccv record) ++
      encode_uint 4 (order_security_code record) ++
      encode_bytes 4 (external_member record) ++
      encode_uint 4 (secondary_order_id_2 record) ++
      encode_uint 4 (entry_date_2 record) ++
      encode_uint 4 (priority_2 record) ++
      encode_uint 8 (price_2 record) ++
      encode_uint 4 (display_qty_2 record) ++
      encode_uint 4 (order_id_2 record) ++
      encode_uint 4 (secondary_exec_id_2 record) ++
      encode_uint 4 (order_qty_2 record) ++
      encode_bytes 1 (ord_status_2 record) ++
      encode_bytes 1 (ccp_code_2 record) ++
      encode_bytes 1 (aggressor_indicator_2 record) ++
      encode_uint 4 (request_id_2 record) ++
      encode_uint 2 (client_data_id_2 record) ++
      encode_uint 1 (algorithmic_trade_indicator_2 record) ++
      encode_uint 4 (client_id_2 record) ++
      encode_bytes 16 (account_bolsa_2 record) ++
      encode_bytes 5 (account_2 record) ++
      encode_uint 1 (dea_flag_2 record) ++
      encode_uint 4 (decisor_id_2 record) ++
      encode_uint 4 (executor_id_2 record) ++
      encode_uint 1 (liquidity_provision_activity_2 record) ++
      encode_bytes 4 (give_in_member_2 record) ++
      encode_bytes 10 (firm_mnemonic_2 record) ++
      encode_bytes 18 (alloc_text_2 record) ++
      encode_bytes 1 (last_capacity_2 record) ++
      encode_uint 2 (self_match_prevention_id_2 record) ++
      encode_bytes 1 (automatic_order_filter_flag_2 record) ++
      encode_bytes 1 (received_dept_id_2 record) ++
      encode_bytes 1 (persistence_2 record) ++
      encode_bytes 1 (account_type_2 record) ++
      encode_bytes 1 (self_match_prevention_type_2 record) ++
      encode_bytes 4 (member_2 record) ++
      encode_bytes 3 (trader_2 record) ++
      encode_bytes 1 (sub_member_2 record) ++
      encode_uint 4 (cross_id_2 record) ++
      encode_bytes 1 (bolsa_code_2 record) ++
      encode_bytes 11 (csdbic_2 record) ++
      encode_bytes 11 (participant_2 record) ++
      encode_bytes 35 (cta_liq_2 record) ++
      encode_bytes 20 (ccv_2 record) ++
      encode_uint 4 (order_security_code_2 record) ++
      encode_bytes 4 (external_member_2 record).

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
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (buyer_bolsa_code_value, bytes) =>
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
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (publish_date_and_time_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (trade_date_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_session_date_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (volume_float_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (sicav_fund_counterparty_side_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (amended_trade_type_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (exec_ref_id_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (amended_trade_date_value, bytes) =>
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
                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (order_id_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (secondary_exec_id_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (order_qty_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ord_status_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ccp_code_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (aggressor_indicator_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (request_id_value, bytes) =>
                                                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (client_data_id_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (algorithmic_trade_indicator_value, bytes) =>
                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (client_id_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 16 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (account_bolsa_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (account_value, bytes) =>
                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (dea_flag_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (decisor_id_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (executor_id_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (liquidity_provision_activity_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (give_in_member_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (firm_mnemonic_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 18 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (alloc_text_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (last_capacity_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (self_match_prevention_id_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (automatic_order_filter_flag_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (received_dept_id_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (persistence_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (account_type_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (self_match_prevention_type_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (member_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (trader_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (sub_member_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (cross_id_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (bolsa_code_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (csdbic_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (participant_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 35 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (cta_liq_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (ccv_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (order_security_code_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (external_member_value, bytes) =>
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
                                                                                                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (order_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (secondary_exec_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (order_qty_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (ord_status_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (ccp_code_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (aggressor_indicator_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (request_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (client_data_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (algorithmic_trade_indicator_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (client_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 16 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (account_bolsa_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (account_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (dea_flag_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (decisor_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (executor_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                  | Some (liquidity_provision_activity_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                      | Some (give_in_member_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 10 bytes with
                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                          | Some (firm_mnemonic_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 18 bytes with
                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                              | Some (alloc_text_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (last_capacity_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                      | Some (self_match_prevention_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                          | Some (automatic_order_filter_flag_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                              | Some (received_dept_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (persistence_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (account_type_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (self_match_prevention_type_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (member_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (trader_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (sub_member_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (cross_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (bolsa_code_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (csdbic_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (participant_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 35 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (cta_liq_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (ccv_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (order_security_code_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (external_member_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; volume_float := volume_float_value; sicav_fund_counterparty_side := sicav_fund_counterparty_side_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; give_in_member := give_in_member_value; firm_mnemonic := firm_mnemonic_value; alloc_text := alloc_text_value; last_capacity := last_capacity_value; self_match_prevention_id := self_match_prevention_id_value; automatic_order_filter_flag := automatic_order_filter_flag_value; received_dept_id := received_dept_id_value; persistence := persistence_value; account_type := account_type_value; self_match_prevention_type := self_match_prevention_type_value; member := member_value; trader := trader_value; sub_member := sub_member_value; cross_id := cross_id_value; bolsa_code := bolsa_code_value; csdbic := csdbic_value; participant := participant_value; cta_liq := cta_liq_value; ccv := ccv_value; order_security_code := order_security_code_value; external_member := external_member_value; secondary_order_id_2 := secondary_order_id_2_value; entry_date_2 := entry_date_2_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; order_id_2 := order_id_2_value; secondary_exec_id_2 := secondary_exec_id_2_value; order_qty_2 := order_qty_2_value; ord_status_2 := ord_status_2_value; ccp_code_2 := ccp_code_2_value; aggressor_indicator_2 := aggressor_indicator_2_value; request_id_2 := request_id_2_value; client_data_id_2 := client_data_id_2_value; algorithmic_trade_indicator_2 := algorithmic_trade_indicator_2_value; client_id_2 := client_id_2_value; account_bolsa_2 := account_bolsa_2_value; account_2 := account_2_value; dea_flag_2 := dea_flag_2_value; decisor_id_2 := decisor_id_2_value; executor_id_2 := executor_id_2_value; liquidity_provision_activity_2 := liquidity_provision_activity_2_value; give_in_member_2 := give_in_member_2_value; firm_mnemonic_2 := firm_mnemonic_2_value; alloc_text_2 := alloc_text_2_value; last_capacity_2 := last_capacity_2_value; self_match_prevention_id_2 := self_match_prevention_id_2_value; automatic_order_filter_flag_2 := automatic_order_filter_flag_2_value; received_dept_id_2 := received_dept_id_2_value; persistence_2 := persistence_2_value; account_type_2 := account_type_2_value; self_match_prevention_type_2 := self_match_prevention_type_2_value; member_2 := member_2_value; trader_2 := trader_2_value; sub_member_2 := sub_member_2_value; cross_id_2 := cross_id_2_value; bolsa_code_2 := bolsa_code_2_value; csdbic_2 := csdbic_2_value; participant_2 := participant_2_value; cta_liq_2 := cta_liq_2_value; ccv_2 := ccv_2_value; order_security_code_2 := order_security_code_2_value; external_member_2 := external_member_2_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 536.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 [bound_95 [bound_96 [bound_97 [bound_98 [bound_99 [bound_100 [bound_101 [bound_102 [bound_103 [bound_104 [bound_105 [bound_106 [bound_107 [bound_108 [bound_109 [bound_110 [bound_111 bound_112]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
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
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_uint by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_uint by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_uint by exact bound_76.
      rewrite decode_encode_uint by exact bound_77.
      rewrite decode_encode_uint by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_bytes by exact bound_80.
      rewrite decode_encode_bytes by exact bound_81.
      rewrite decode_encode_uint by exact bound_82.
      rewrite decode_encode_uint by exact bound_83.
      rewrite decode_encode_uint by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_bytes by exact bound_86.
      rewrite decode_encode_bytes by exact bound_87.
      rewrite decode_encode_uint by exact bound_88.
      rewrite decode_encode_uint by exact bound_89.
      rewrite decode_encode_uint by exact bound_90.
      rewrite decode_encode_uint by exact bound_91.
      rewrite decode_encode_bytes by exact bound_92.
      rewrite decode_encode_bytes by exact bound_93.
      rewrite decode_encode_bytes by exact bound_94.
      rewrite decode_encode_bytes by exact bound_95.
      rewrite decode_encode_uint by exact bound_96.
      rewrite decode_encode_bytes by exact bound_97.
      rewrite decode_encode_bytes by exact bound_98.
      rewrite decode_encode_bytes by exact bound_99.
      rewrite decode_encode_bytes by exact bound_100.
      rewrite decode_encode_bytes by exact bound_101.
      rewrite decode_encode_bytes by exact bound_102.
      rewrite decode_encode_bytes by exact bound_103.
      rewrite decode_encode_bytes by exact bound_104.
      rewrite decode_encode_uint by exact bound_105.
      rewrite decode_encode_bytes by exact bound_106.
      rewrite decode_encode_bytes by exact bound_107.
      rewrite decode_encode_bytes by exact bound_108.
      rewrite decode_encode_bytes by exact bound_109.
      rewrite decode_encode_bytes by exact bound_110.
      rewrite decode_encode_uint by exact bound_111.
      rewrite decode_encode_bytes by exact bound_112.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.

  Module ExecutionPrivateInformation1LegBuyOrderEntryMessage.

    (** Sent by the server to inform about a trade where the user is involved as Buyer. Shares the same layout as the next message *)
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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ccp_code : list byte;
      aggressor_indicator : list byte;
      request_id : N;
      client_data_id : N;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ccp_code record) = 1 /\
      Datatypes.length (aggressor_indicator record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N.

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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ccp_code record) ++
      encode_bytes 1 (aggressor_indicator record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record).

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
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (buyer_bolsa_code_value, bytes) =>
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
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (order_id_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (secondary_exec_id_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (order_qty_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ord_status_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ccp_code_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (aggressor_indicator_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (request_id_value, bytes) =>
                                                                                                                      match decode_uint 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (client_data_id_value, bytes) =>
                                                                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value |}, bytes)
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 bound_28]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionPrivateInformation1LegBuyOrderEntryMessage.

  Module ExecutionPrivateInformation1LegSellOrderEntryMessage.

    (** Sent by the server to inform about a trade where the user is involved as Seller *)
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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      order_id : N;
      secondary_exec_id : N;
      order_qty : N;
      ord_status : list byte;
      ccp_code : list byte;
      aggressor_indicator : list byte;
      request_id : N;
      client_data_id : N;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (secondary_exec_id record < 256 ^ N.of_nat 4)%N /\
      (order_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ord_status record) = 1 /\
      Datatypes.length (ccp_code record) = 1 /\
      Datatypes.length (aggressor_indicator record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (client_data_id record < 256 ^ N.of_nat 2)%N.

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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (secondary_exec_id record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (ord_status record) ++
      encode_bytes 1 (ccp_code record) ++
      encode_bytes 1 (aggressor_indicator record) ++
      encode_uint 4 (request_id record) ++
      encode_uint 2 (client_data_id record).

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
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (buyer_bolsa_code_value, bytes) =>
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
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (order_id_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (secondary_exec_id_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (order_qty_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ord_status_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ccp_code_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (aggressor_indicator_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (request_id_value, bytes) =>
                                                                                                                      match decode_uint 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (client_data_id_value, bytes) =>
                                                                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value |}, bytes)
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 bound_28]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionPrivateInformation1LegSellOrderEntryMessage.

End BmeEquitiesOrderEntryV16.
