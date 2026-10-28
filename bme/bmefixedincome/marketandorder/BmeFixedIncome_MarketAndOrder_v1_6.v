From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsas y Mercados Españoles BME Fixed Income Market And Order

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

Module BmeFixedIncomeMarketAndOrderV16.

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
      account_member : list byte;
      last_capacity : list byte;
      received_dept_id : list byte;
      persistence : list byte;
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
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
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
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
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
                                              | Some (account_member_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (last_capacity_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (received_dept_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (persistence_value, bytes) =>
                                                              match decode_bytes 15 bytes with
                                                              | None => None
                                                              | Some (client_data_reference_value, bytes) =>
                                                                  Some ({| request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; account_member := account_member_value; last_capacity := last_capacity_value; received_dept_id := received_dept_id_value; persistence := persistence_value; client_data_reference := client_data_reference_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_bytes by exact bound_14.
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
      Datatypes.length (time_in_force record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 2 (client_data_id record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (time_in_force record).

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
                                      Some ({| request_id := request_id_value; security_code := security_code_value; client_data_id := client_data_id_value; order_id := order_id_value; side := side_value; price := price_value; order_qty := order_qty_value; time_in_force := time_in_force_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
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
      algorithmic_trade_indicator : N;
      client_id : N;
      account_bolsa : list byte;
      account : list byte;
      dea_flag : N;
      decisor_id : N;
      executor_id : N;
      liquidity_provision_activity : N;
      account_member : list byte;
      last_capacity : list byte;
      received_dept_id : list byte;
      persistence : list byte;
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
      (algorithmic_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account record) = 5 /\
      (dea_flag record < 256 ^ N.of_nat 1)%N /\
      (decisor_id record < 256 ^ N.of_nat 4)%N /\
      (executor_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_provision_activity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (client_data_reference record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_qty record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_uint 1 (algorithmic_trade_indicator record) ++
      encode_uint 4 (client_id record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 5 (account record) ++
      encode_uint 1 (dea_flag record) ++
      encode_uint 4 (decisor_id record) ++
      encode_uint 4 (executor_id record) ++
      encode_uint 1 (liquidity_provision_activity record) ++
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
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
                                                                  | Some (account_member_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (last_capacity_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (received_dept_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (persistence_value, bytes) =>
                                                                                  match decode_bytes 15 bytes with
                                                                                  | None => None
                                                                                  | Some (client_data_reference_value, bytes) =>
                                                                                      Some ({| request_id := request_id_value; security_code := security_code_value; order_id := order_id_value; side := side_value; price := price_value; order_qty := order_qty_value; time_in_force := time_in_force_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; account_member := account_member_value; last_capacity := last_capacity_value; received_dept_id := received_dept_id_value; persistence := persistence_value; client_data_reference := client_data_reference_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
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
      account_member : list byte;
      last_capacity : list byte;
      received_dept_id : list byte;
      persistence : list byte;
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
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
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
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
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
                                                              | Some (account_member_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (last_capacity_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (received_dept_id_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (persistence_value, bytes) =>
                                                                              match decode_bytes 15 bytes with
                                                                              | None => None
                                                                              | Some (client_data_reference_value, bytes) =>
                                                                                  Some ({| request_id := request_id_value; security_code := security_code_value; order_id := order_id_value; side := side_value; price := price_value; order_qty := order_qty_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; account_member := account_member_value; last_capacity := last_capacity_value; received_dept_id := received_dept_id_value; persistence := persistence_value; client_data_reference := client_data_reference_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_18.
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
      account : list byte;
      security_code : N;
      side : list byte;
      cancellation_type : list byte;
      issuer : list byte;
      account_bolsa : list byte;
      account_member : list byte;
      order_or_quote_cancel : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (account record) = 5 /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (cancellation_type record) = 1 /\
      Datatypes.length (issuer record) = 12 /\
      Datatypes.length (account_bolsa record) = 16 /\
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (order_or_quote_cancel record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_bytes 5 (account record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (cancellation_type record) ++
      encode_bytes 12 (issuer record) ++
      encode_bytes 16 (account_bolsa record) ++
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (order_or_quote_cancel record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (account_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (security_code_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cancellation_type_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (issuer_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (account_bolsa_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (account_member_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (order_or_quote_cancel_value, bytes) =>
                                          Some ({| request_id := request_id_value; account := account_value; security_code := security_code_value; side := side_value; cancellation_type := cancellation_type_value; issuer := issuer_value; account_bolsa := account_bolsa_value; account_member := account_member_value; order_or_quote_cancel := order_or_quote_cancel_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
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
      account_member : list byte;
      last_capacity : list byte;
      received_dept_id : list byte;
      persistence : list byte;
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
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
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
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
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
                                                      | Some (account_member_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (last_capacity_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (received_dept_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (persistence_value, bytes) =>
                                                                      match decode_bytes 15 bytes with
                                                                      | None => None
                                                                      | Some (client_data_reference_value, bytes) =>
                                                                          Some ({| sequence_number := sequence_number_value; request_id := request_id_value; status := status_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; account_member := account_member_value; last_capacity := last_capacity_value; received_dept_id := received_dept_id_value; persistence := persistence_value; client_data_reference := client_data_reference_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
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
      rewrite decode_encode_bytes by exact bound_16.
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
      alt_price : N;
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
      (alt_price record < 256 ^ N.of_nat 8)%N /\
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
      encode_uint 8 (alt_price record) ++
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
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (alt_price_value, bytes) =>
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
                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; side := side_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; exec_type := exec_type_value; request_id := request_id_value; client_data_id := client_data_id_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
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
      alt_price : N;
      priority_2 : N;
      price_2 : N;
      display_qty_2 : N;
      alt_price_2 : N;
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
      (alt_price record < 256 ^ N.of_nat 8)%N /\
      (priority_2 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 8)%N /\
      (display_qty_2 record < 256 ^ N.of_nat 4)%N /\
      (alt_price_2 record < 256 ^ N.of_nat 8)%N /\
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
      encode_uint 8 (alt_price record) ++
      encode_uint 4 (priority_2 record) ++
      encode_uint 8 (price_2 record) ++
      encode_uint 4 (display_qty_2 record) ++
      encode_uint 8 (alt_price_2 record) ++
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
                                                                                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; secondary_order_id := secondary_order_id_value; secondary_order_id_2 := secondary_order_id_2_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; alt_price_2 := alt_price_2_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ord_rej_reason := ord_rej_reason_value; exec_type := exec_type_value; order_id_2 := order_id_2_value; secondary_exec_id_2 := secondary_exec_id_2_value; order_qty_2 := order_qty_2_value; ord_status_2 := ord_status_2_value; ord_rej_reason_2 := ord_rej_reason_2_value; exec_type_2 := exec_type_2_value; request_id := request_id_value; client_data_id := client_data_id_value |}, bytes)
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 108.
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
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
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
      cancellation_type : list byte;
      order_or_quote_cancel : list byte;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trading_unit record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (cancellation_type record) = 1 /\
      Datatypes.length (order_or_quote_cancel record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 1 (trading_unit record) ++
      encode_bytes 1 (cancellation_type record) ++
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
                  | Some (cancellation_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_or_quote_cancel_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (request_id_value, bytes) =>
                              Some ({| sequence_number := sequence_number_value; transaction_date_and_time := transaction_date_and_time_value; trading_unit := trading_unit_value; cancellation_type := cancellation_type_value; order_or_quote_cancel := order_or_quote_cancel_value; request_id := request_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
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
      alt_price_2 : N;
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
      (alt_price_2 record < 256 ^ N.of_nat 8)%N /\
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
      encode_uint 8 (alt_price_2 record) ++
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
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (alt_price_2_value, bytes) =>
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
                                                                                                                                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; secondary_order_id_2 := secondary_order_id_2_value; entry_date_2 := entry_date_2_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; alt_price_2 := alt_price_2_value; order_id_2 := order_id_2_value; secondary_exec_id_2 := secondary_exec_id_2_value; order_qty_2 := order_qty_2_value; ord_status_2 := ord_status_2_value; ccp_code_2 := ccp_code_2_value; aggressor_indicator_2 := aggressor_indicator_2_value; request_id_2 := request_id_2_value; client_data_id_2 := client_data_id_2_value |}, bytes)
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 184.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 bound_45]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
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
      rewrite decode_encode_bytes by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
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
      broker_trader : list byte;
      broker_text : list byte;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      alt_price : N;
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
      account_member : list byte;
      last_capacity : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      member : list byte;
      trader : list byte;
      sub_member : list byte;
      cross_id : N;
      order_security_code : N;
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
      (amended_trade_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (broker_trader record) = 3 /\
      Datatypes.length (broker_text record) = 15 /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (alt_price record < 256 ^ N.of_nat 8)%N /\
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
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (member record) = 4 /\
      Datatypes.length (trader record) = 3 /\
      Datatypes.length (sub_member record) = 1 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (order_security_code record < 256 ^ N.of_nat 4)%N.

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
      encode_uint 4 (amended_trade_date record) ++
      encode_bytes 3 (broker_trader record) ++
      encode_bytes 15 (broker_text record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 8 (alt_price record) ++
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
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 4 (member record) ++
      encode_bytes 3 (trader record) ++
      encode_bytes 1 (sub_member record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (order_security_code record).

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
                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (broker_trader_value, bytes) =>
                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (broker_text_value, bytes) =>
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
                                                                                                                                                                                                                                      | Some (account_member_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (last_capacity_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (received_dept_id_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (persistence_value, bytes) =>
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
                                                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (order_security_code_value, bytes) =>
                                                                                                                                                                                                                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; post_deferral_publication_type := post_deferral_publication_type_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; settl_date_2 := settl_date_2_value; end_cash := end_cash_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value; broker_trader := broker_trader_value; broker_text := broker_text_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; account_member := account_member_value; last_capacity := last_capacity_value; received_dept_id := received_dept_id_value; persistence := persistence_value; member := member_value; trader := trader_value; sub_member := sub_member_value; cross_id := cross_id_value; order_security_code := order_security_code_value |}, bytes)
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 255.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 bound_64]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
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
      broker_trader : list byte;
      broker_text : list byte;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      alt_price : N;
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
      account_member : list byte;
      last_capacity : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      member : list byte;
      trader : list byte;
      sub_member : list byte;
      cross_id : N;
      order_security_code : N;
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
      (amended_trade_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (broker_trader record) = 3 /\
      Datatypes.length (broker_text record) = 15 /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (alt_price record < 256 ^ N.of_nat 8)%N /\
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
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (member record) = 4 /\
      Datatypes.length (trader record) = 3 /\
      Datatypes.length (sub_member record) = 1 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (order_security_code record < 256 ^ N.of_nat 4)%N.

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
      encode_uint 4 (amended_trade_date record) ++
      encode_bytes 3 (broker_trader record) ++
      encode_bytes 15 (broker_text record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 8 (alt_price record) ++
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
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 4 (member record) ++
      encode_bytes 3 (trader record) ++
      encode_bytes 1 (sub_member record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (order_security_code record).

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
                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (broker_trader_value, bytes) =>
                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (broker_text_value, bytes) =>
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
                                                                                                                                                                                                                                      | Some (account_member_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (last_capacity_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (received_dept_id_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (persistence_value, bytes) =>
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
                                                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (order_security_code_value, bytes) =>
                                                                                                                                                                                                                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; post_deferral_publication_type := post_deferral_publication_type_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; settl_date_2 := settl_date_2_value; end_cash := end_cash_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value; broker_trader := broker_trader_value; broker_text := broker_text_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; account_member := account_member_value; last_capacity := last_capacity_value; received_dept_id := received_dept_id_value; persistence := persistence_value; member := member_value; trader := trader_value; sub_member := sub_member_value; cross_id := cross_id_value; order_security_code := order_security_code_value |}, bytes)
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 255.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 bound_64]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
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
      broker_trader : list byte;
      broker_text : list byte;
      secondary_order_id : N;
      entry_date : N;
      priority : N;
      price : N;
      display_qty : N;
      alt_price : N;
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
      account_member : list byte;
      last_capacity : list byte;
      received_dept_id : list byte;
      persistence : list byte;
      member : list byte;
      trader : list byte;
      sub_member : list byte;
      cross_id : N;
      order_security_code : N;
      secondary_order_id_2 : N;
      entry_date_2 : N;
      priority_2 : N;
      price_2 : N;
      display_qty_2 : N;
      alt_price_2 : N;
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
      account_member_2 : list byte;
      last_capacity_2 : list byte;
      received_dept_id_2 : list byte;
      persistence_2 : list byte;
      member_2 : list byte;
      trader_2 : list byte;
      sub_member_2 : list byte;
      cross_id_2 : N;
      order_security_code_2 : N;
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
      (amended_trade_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (broker_trader record) = 3 /\
      Datatypes.length (broker_text record) = 15 /\
      (secondary_order_id record < 256 ^ N.of_nat 4)%N /\
      (entry_date record < 256 ^ N.of_nat 4)%N /\
      (priority record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      (alt_price record < 256 ^ N.of_nat 8)%N /\
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
      Datatypes.length (account_member record) = 4 /\
      Datatypes.length (last_capacity record) = 1 /\
      Datatypes.length (received_dept_id record) = 1 /\
      Datatypes.length (persistence record) = 1 /\
      Datatypes.length (member record) = 4 /\
      Datatypes.length (trader record) = 3 /\
      Datatypes.length (sub_member record) = 1 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (order_security_code record < 256 ^ N.of_nat 4)%N /\
      (secondary_order_id_2 record < 256 ^ N.of_nat 4)%N /\
      (entry_date_2 record < 256 ^ N.of_nat 4)%N /\
      (priority_2 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 8)%N /\
      (display_qty_2 record < 256 ^ N.of_nat 4)%N /\
      (alt_price_2 record < 256 ^ N.of_nat 8)%N /\
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
      Datatypes.length (account_member_2 record) = 4 /\
      Datatypes.length (last_capacity_2 record) = 1 /\
      Datatypes.length (received_dept_id_2 record) = 1 /\
      Datatypes.length (persistence_2 record) = 1 /\
      Datatypes.length (member_2 record) = 4 /\
      Datatypes.length (trader_2 record) = 3 /\
      Datatypes.length (sub_member_2 record) = 1 /\
      (cross_id_2 record < 256 ^ N.of_nat 4)%N /\
      (order_security_code_2 record < 256 ^ N.of_nat 4)%N.

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
      encode_uint 4 (amended_trade_date record) ++
      encode_bytes 3 (broker_trader record) ++
      encode_bytes 15 (broker_text record) ++
      encode_uint 4 (secondary_order_id record) ++
      encode_uint 4 (entry_date record) ++
      encode_uint 4 (priority record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (display_qty record) ++
      encode_uint 8 (alt_price record) ++
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
      encode_bytes 4 (account_member record) ++
      encode_bytes 1 (last_capacity record) ++
      encode_bytes 1 (received_dept_id record) ++
      encode_bytes 1 (persistence record) ++
      encode_bytes 4 (member record) ++
      encode_bytes 3 (trader record) ++
      encode_bytes 1 (sub_member record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (order_security_code record) ++
      encode_uint 4 (secondary_order_id_2 record) ++
      encode_uint 4 (entry_date_2 record) ++
      encode_uint 4 (priority_2 record) ++
      encode_uint 8 (price_2 record) ++
      encode_uint 4 (display_qty_2 record) ++
      encode_uint 8 (alt_price_2 record) ++
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
      encode_bytes 4 (account_member_2 record) ++
      encode_bytes 1 (last_capacity_2 record) ++
      encode_bytes 1 (received_dept_id_2 record) ++
      encode_bytes 1 (persistence_2 record) ++
      encode_bytes 4 (member_2 record) ++
      encode_bytes 3 (trader_2 record) ++
      encode_bytes 1 (sub_member_2 record) ++
      encode_uint 4 (cross_id_2 record) ++
      encode_uint 4 (order_security_code_2 record).

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
                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (broker_trader_value, bytes) =>
                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (broker_text_value, bytes) =>
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
                                                                                                                                                                                                                                      | Some (account_member_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (last_capacity_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (received_dept_id_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (persistence_value, bytes) =>
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
                                                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (order_security_code_value, bytes) =>
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
                                                                                                                                                                                                                                                                                                                                                                  | Some (account_member_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (last_capacity_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (received_dept_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (persistence_2_value, bytes) =>
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
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (order_security_code_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; post_deferral_publication_type := post_deferral_publication_type_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; settl_date_2 := settl_date_2_value; end_cash := end_cash_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value; broker_trader := broker_trader_value; broker_text := broker_text_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; algorithmic_trade_indicator := algorithmic_trade_indicator_value; client_id := client_id_value; account_bolsa := account_bolsa_value; account := account_value; dea_flag := dea_flag_value; decisor_id := decisor_id_value; executor_id := executor_id_value; liquidity_provision_activity := liquidity_provision_activity_value; account_member := account_member_value; last_capacity := last_capacity_value; received_dept_id := received_dept_id_value; persistence := persistence_value; member := member_value; trader := trader_value; sub_member := sub_member_value; cross_id := cross_id_value; order_security_code := order_security_code_value; secondary_order_id_2 := secondary_order_id_2_value; entry_date_2 := entry_date_2_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; alt_price_2 := alt_price_2_value; order_id_2 := order_id_2_value; secondary_exec_id_2 := secondary_exec_id_2_value; order_qty_2 := order_qty_2_value; ord_status_2 := ord_status_2_value; ccp_code_2 := ccp_code_2_value; aggressor_indicator_2 := aggressor_indicator_2_value; request_id_2 := request_id_2_value; client_data_id_2 := client_data_id_2_value; algorithmic_trade_indicator_2 := algorithmic_trade_indicator_2_value; client_id_2 := client_id_2_value; account_bolsa_2 := account_bolsa_2_value; account_2 := account_2_value; dea_flag_2 := dea_flag_2_value; decisor_id_2 := decisor_id_2_value; executor_id_2 := executor_id_2_value; liquidity_provision_activity_2 := liquidity_provision_activity_2_value; account_member_2 := account_member_2_value; last_capacity_2 := last_capacity_2_value; received_dept_id_2 := received_dept_id_2_value; persistence_2 := persistence_2_value; member_2 := member_2_value; trader_2 := trader_2_value; sub_member_2 := sub_member_2_value; cross_id_2 := cross_id_2_value; order_security_code_2 := order_security_code_2_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 367.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 bound_95]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
      rewrite decode_encode_uint by exact bound_65.
      rewrite decode_encode_uint by exact bound_66.
      rewrite decode_encode_uint by exact bound_67.
      rewrite decode_encode_uint by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_uint by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_uint by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_bytes by exact bound_75.
      rewrite decode_encode_bytes by exact bound_76.
      rewrite decode_encode_uint by exact bound_77.
      rewrite decode_encode_uint by exact bound_78.
      rewrite decode_encode_uint by exact bound_79.
      rewrite decode_encode_uint by exact bound_80.
      rewrite decode_encode_bytes by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_uint by exact bound_83.
      rewrite decode_encode_uint by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_uint by exact bound_86.
      rewrite decode_encode_bytes by exact bound_87.
      rewrite decode_encode_bytes by exact bound_88.
      rewrite decode_encode_bytes by exact bound_89.
      rewrite decode_encode_bytes by exact bound_90.
      rewrite decode_encode_bytes by exact bound_91.
      rewrite decode_encode_bytes by exact bound_92.
      rewrite decode_encode_bytes by exact bound_93.
      rewrite decode_encode_uint by exact bound_94.
      rewrite decode_encode_uint by exact bound_95.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTradeAmendmentOrCancellation2LegsPrivateInformationMessage.

  Module ExecutionPrivateInformation1LegBuyMarketOrderMessage.

    (** Sent by the server to inform about a trade where the user is involved as Buyer. In the order where the member is not involved, only the market information is sent, so that the application can update the books *)
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
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (alt_price_2_value, bytes) =>
                                                                                                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; order_id := order_id_value; secondary_exec_id := secondary_exec_id_value; order_qty := order_qty_value; ord_status := ord_status_value; ccp_code := ccp_code_value; aggressor_indicator := aggressor_indicator_value; request_id := request_id_value; client_data_id := client_data_id_value; secondary_order_id_2 := secondary_order_id_2_value; entry_date_2 := entry_date_2_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; alt_price_2 := alt_price_2_value |}, bytes)
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 163.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 bound_37]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionPrivateInformation1LegBuyMarketOrderMessage.

  Module ExecutionPrivateInformation1LegSellMarketOrderMessage.

    (** Sent by the server to inform about a trade where the user is involved as Seller. In the order where the member is not involved, only the market information is sent, so that the application can update the books *)
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
      (alt_price_2 record < 256 ^ N.of_nat 8)%N /\
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
      encode_uint 8 (alt_price_2 record) ++
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
                                                                                                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; alt_last_px := alt_last_px_value; accrued_interest_amt := accrued_interest_amt_value; accrued_interest_rate_p_8 := accrued_interest_rate_p_8_value; settl_date := settl_date_value; transaction_category := transaction_category_value; secondary_order_id := secondary_order_id_value; entry_date := entry_date_value; priority := priority_value; price := price_value; display_qty := display_qty_value; alt_price := alt_price_value; secondary_order_id_2 := secondary_order_id_2_value; entry_date_2 := entry_date_2_value; priority_2 := priority_2_value; price_2 := price_2_value; display_qty_2 := display_qty_2_value; alt_price_2 := alt_price_2_value; order_id_2 := order_id_2_value; secondary_exec_id_2 := secondary_exec_id_2_value; order_qty_2 := order_qty_2_value; ord_status_2 := ord_status_2_value; ccp_code_2 := ccp_code_2_value; aggressor_indicator_2 := aggressor_indicator_2_value; request_id_2 := request_id_2_value; client_data_id_2 := client_data_id_2_value |}, bytes)
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 163.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 bound_37]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionPrivateInformation1LegSellMarketOrderMessage.

End BmeFixedIncomeMarketAndOrderV16.
