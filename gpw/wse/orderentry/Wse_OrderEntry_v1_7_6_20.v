From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Native Order Gateway

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
      - a field read in bits
      - a run counted by a field
  *)

Module WseOrderEntryV17620.

  Module MessageHeader.

    (** Every order gateway message opens with the same 24 byte header *)
    Record t := {
      message_length : N;
      message_type : N;
      sequence_number : N;
      timestamp : N;
      source_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (source_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (message_type record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (source_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (sequence_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (source_timestamp_value, bytes) =>
                          Some ({| message_length := message_length_value; message_type := message_type_value; sequence_number := sequence_number_value; timestamp := timestamp_value; source_timestamp := source_timestamp_value |}, bytes)
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

  End MessageHeader.

  Module Login.

    (** The login message authenticates a user establishing a connection to the trading port service. The login message must be the first message sent by the client application to request the initiation of a trading port session *)
    Record t := {
      version : N;
      token : list byte;
      connection_id : N;
      next_expected_seq_num : N;
      last_sent_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (token record) = 8 /\
      (connection_id record < 256 ^ N.of_nat 2)%N /\
      (next_expected_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_sent_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (version record) ++
      encode_bytes 8 (token record) ++
      encode_uint 2 (connection_id record) ++
      encode_uint 4 (next_expected_seq_num record) ++
      encode_uint 4 (last_sent_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (token_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (connection_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (next_expected_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (last_sent_seq_num_value, bytes) =>
                          Some ({| version := version_value; token := token_value; connection_id := connection_id_value; next_expected_seq_num := next_expected_seq_num_value; last_sent_seq_num := last_sent_seq_num_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Login.

  Module LoginResponse.

    (** The login response message. The result field describes the login status, indicating whether the login was successful or not (i.e. successful login) *)
    Record t := {
      result_login_result : N;
      next_expected_seq_num : N;
      last_replay_seq_num : N;
      session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (result_login_result record < 256 ^ N.of_nat 1)%N /\
      (next_expected_seq_num record < 256 ^ N.of_nat 4)%N /\
      (last_replay_seq_num record < 256 ^ N.of_nat 4)%N /\
      (session_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (result_login_result record) ++
      encode_uint 4 (next_expected_seq_num record) ++
      encode_uint 4 (last_replay_seq_num record) ++
      encode_uint 2 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (result_login_result_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (next_expected_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (last_replay_seq_num_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (session_id_value, bytes) =>
                      Some ({| result_login_result := result_login_result_value; next_expected_seq_num := next_expected_seq_num_value; last_replay_seq_num := last_replay_seq_num_value; session_id := session_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End LoginResponse.

  Module ConnectionClose.

    (** The ConnectionClose message confirms the termination of a session through the trading port service *)
    Record t := {
      reason_connection_close_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reason_connection_close_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reason_connection_close_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reason_connection_close_reason_value, bytes) =>
          Some ({| reason_connection_close_reason := reason_connection_close_reason_value |}, bytes)
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

  End ConnectionClose.

  Module Reject.

    (** The reject message is sent by the trading port service when receiving an erroneous message that cannot be further processed *)
    Record t := {
      ref_seq_num : N;
      reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ref_seq_num record < 256 ^ N.of_nat 4)%N /\
      (reject_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (ref_seq_num record) ++
      encode_uint 1 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (ref_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (reject_reason_value, bytes) =>
              Some ({| ref_seq_num := ref_seq_num_value; reject_reason := reject_reason_value |}, bytes)
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

  End Reject.

  Module Test.

    (** The internal message for a test purpose *)
    Record t := {
      target_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (target_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (target_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (target_timestamp_value, bytes) =>
          Some ({| target_timestamp := target_timestamp_value |}, bytes)
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

  End Test.

  Module TestEvent.

    (** Test event *)
    Record t := {
      scenario_name : list byte;
      event_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (scenario_name record) = 200 /\
      (event_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 200 (scenario_name record) ++
      encode_uint 1 (event_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 200 bytes with
      | None => None
      | Some (scenario_name_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (event_type_value, bytes) =>
              Some ({| scenario_name := scenario_name_value; event_type := event_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 201.
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

  End TestEvent.

  Module TradingSessionStatus.

    (** The Trading Session Status provides information on the status of a trading session *)
    Record t := {
      market_id : list byte;
      date : N;
      trading_session_event : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_id record) = 4 /\
      (date record < 256 ^ N.of_nat 4)%N /\
      (trading_session_event record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (market_id record) ++
      encode_uint 4 (date record) ++
      encode_uint 1 (trading_session_event record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_event_value, bytes) =>
                  Some ({| market_id := market_id_value; date := date_value; trading_session_event := trading_session_event_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End TradingSessionStatus.

  Module Client.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End Client.

  Module ExecutingTrader.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader.

  Module InvestmentDecisionMaker.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End InvestmentDecisionMaker.

  Module MifidFields.

    (** MifidFields *)
    Record t := {
      client : Client.t;
      executing_trader : ExecutingTrader.t;
      investment_decision_maker : InvestmentDecisionMaker.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Client.bounded (client record) /\
      ExecutingTrader.bounded (executing_trader record) /\
      InvestmentDecisionMaker.bounded (investment_decision_maker record).

    Definition encode (record : t) : list byte :=
      Client.encode (client record) ++
      ExecutingTrader.encode (executing_trader record) ++
      InvestmentDecisionMaker.encode (investment_decision_maker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Client.decode bytes with
      | None => None
      | Some (client_value, bytes) =>
          match ExecutingTrader.decode bytes with
          | None => None
          | Some (executing_trader_value, bytes) =>
              match InvestmentDecisionMaker.decode bytes with
              | None => None
              | Some (investment_decision_maker_value, bytes) =>
                  Some ({| client := client_value; executing_trader := executing_trader_value; investment_decision_maker := investment_decision_maker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Client.encode_length, !ExecutingTrader.encode_length, !InvestmentDecisionMaker.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Client.decode_encode by exact bound_0.
      rewrite ExecutingTrader.decode_encode by exact bound_1.
      rewrite InvestmentDecisionMaker.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Client.eq_dec | apply ExecutingTrader.eq_dec | apply InvestmentDecisionMaker.eq_dec]. Defined.

  End MifidFields.

  Module Client2.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End Client2.

  Module ExecutingTrader2.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader2.

  Module InvestmentDecisionMaker2.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End InvestmentDecisionMaker2.

  Module MifidFields2.

    (** MifidFields *)
    Record t := {
      client : Client2.t;
      executing_trader : ExecutingTrader2.t;
      investment_decision_maker : InvestmentDecisionMaker2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Client2.bounded (client record) /\
      ExecutingTrader2.bounded (executing_trader record) /\
      InvestmentDecisionMaker2.bounded (investment_decision_maker record).

    Definition encode (record : t) : list byte :=
      Client2.encode (client record) ++
      ExecutingTrader2.encode (executing_trader record) ++
      InvestmentDecisionMaker2.encode (investment_decision_maker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Client2.decode bytes with
      | None => None
      | Some (client_value, bytes) =>
          match ExecutingTrader2.decode bytes with
          | None => None
          | Some (executing_trader_value, bytes) =>
              match InvestmentDecisionMaker2.decode bytes with
              | None => None
              | Some (investment_decision_maker_value, bytes) =>
                  Some ({| client := client_value; executing_trader := executing_trader_value; investment_decision_maker := investment_decision_maker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Client2.encode_length, !ExecutingTrader2.encode_length, !InvestmentDecisionMaker2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Client2.decode_encode by exact bound_0.
      rewrite ExecutingTrader2.decode_encode by exact bound_1.
      rewrite InvestmentDecisionMaker2.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Client2.eq_dec | apply ExecutingTrader2.eq_dec | apply InvestmentDecisionMaker2.eq_dec]. Defined.

  End MifidFields2.

  Module Client3.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End Client3.

  Module ExecutingTrader3.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader3.

  Module InvestmentDecisionMaker3.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End InvestmentDecisionMaker3.

  Module MifidFields3.

    (** MifidFields *)
    Record t := {
      client : Client3.t;
      executing_trader : ExecutingTrader3.t;
      investment_decision_maker : InvestmentDecisionMaker3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Client3.bounded (client record) /\
      ExecutingTrader3.bounded (executing_trader record) /\
      InvestmentDecisionMaker3.bounded (investment_decision_maker record).

    Definition encode (record : t) : list byte :=
      Client3.encode (client record) ++
      ExecutingTrader3.encode (executing_trader record) ++
      InvestmentDecisionMaker3.encode (investment_decision_maker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Client3.decode bytes with
      | None => None
      | Some (client_value, bytes) =>
          match ExecutingTrader3.decode bytes with
          | None => None
          | Some (executing_trader_value, bytes) =>
              match InvestmentDecisionMaker3.decode bytes with
              | None => None
              | Some (investment_decision_maker_value, bytes) =>
                  Some ({| client := client_value; executing_trader := executing_trader_value; investment_decision_maker := investment_decision_maker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Client3.encode_length, !ExecutingTrader3.encode_length, !InvestmentDecisionMaker3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Client3.decode_encode by exact bound_0.
      rewrite ExecutingTrader3.decode_encode by exact bound_1.
      rewrite InvestmentDecisionMaker3.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Client3.eq_dec | apply ExecutingTrader3.eq_dec | apply InvestmentDecisionMaker3.eq_dec]. Defined.

  End MifidFields3.

  Module ExecutingTrader4.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader4.

  Module OrderMassCancel.

    (** Message used to cancel multiple existing orders *)
    Record t := {
      mass_cancel_request_type : N;
      target_party_role : N;
      target_party_id : N;
      market_segment_id : N;
      instrument_id : N;
      executing_trader : ExecutingTrader4.t;
      client_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mass_cancel_request_type record < 256 ^ N.of_nat 1)%N /\
      (target_party_role record < 256 ^ N.of_nat 1)%N /\
      (target_party_id record < 256 ^ N.of_nat 4)%N /\
      (market_segment_id record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      ExecutingTrader4.bounded (executing_trader record) /\
      Datatypes.length (client_order_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (mass_cancel_request_type record) ++
      encode_uint 1 (target_party_role record) ++
      encode_uint 4 (target_party_id record) ++
      encode_uint 4 (market_segment_id record) ++
      encode_uint 4 (instrument_id record) ++
      ExecutingTrader4.encode (executing_trader record) ++
      encode_bytes 20 (client_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (mass_cancel_request_type_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (target_party_role_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (target_party_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match ExecutingTrader4.decode bytes with
                          | None => None
                          | Some (executing_trader_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (client_order_id_value, bytes) =>
                                  Some ({| mass_cancel_request_type := mass_cancel_request_type_value; target_party_role := target_party_role_value; target_party_id := target_party_id_value; market_segment_id := market_segment_id_value; instrument_id := instrument_id_value; executing_trader := executing_trader_value; client_order_id := client_order_id_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !ExecutingTrader4.encode_length, !encode_bytes_length. reflexivity.
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
      rewrite ExecutingTrader4.decode_encode by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecutingTrader4.eq_dec]. Defined.

  End OrderMassCancel.

  Module Client4.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End Client4.

  Module ExecutingTrader5.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader5.

  Module InvestmentDecisionMaker4.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End InvestmentDecisionMaker4.

  Module MifidFields4.

    (** MifidFields *)
    Record t := {
      client : Client4.t;
      executing_trader : ExecutingTrader5.t;
      investment_decision_maker : InvestmentDecisionMaker4.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Client4.bounded (client record) /\
      ExecutingTrader5.bounded (executing_trader record) /\
      InvestmentDecisionMaker4.bounded (investment_decision_maker record).

    Definition encode (record : t) : list byte :=
      Client4.encode (client record) ++
      ExecutingTrader5.encode (executing_trader record) ++
      InvestmentDecisionMaker4.encode (investment_decision_maker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Client4.decode bytes with
      | None => None
      | Some (client_value, bytes) =>
          match ExecutingTrader5.decode bytes with
          | None => None
          | Some (executing_trader_value, bytes) =>
              match InvestmentDecisionMaker4.decode bytes with
              | None => None
              | Some (investment_decision_maker_value, bytes) =>
                  Some ({| client := client_value; executing_trader := executing_trader_value; investment_decision_maker := investment_decision_maker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Client4.encode_length, !ExecutingTrader5.encode_length, !InvestmentDecisionMaker4.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Client4.decode_encode by exact bound_0.
      rewrite ExecutingTrader5.decode_encode by exact bound_1.
      rewrite InvestmentDecisionMaker4.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Client4.eq_dec | apply ExecutingTrader5.eq_dec | apply InvestmentDecisionMaker4.eq_dec]. Defined.

  End MifidFields4.

  Module Bid.

    (** QuoteOrder *)
    Record t := {
      price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (price_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              Some ({| price := price_value; quantity := quantity_value |}, bytes)
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

  End Bid.

  Module Ask.

    (** QuoteOrder *)
    Record t := {
      price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (price_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              Some ({| price := price_value; quantity := quantity_value |}, bytes)
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

  End Ask.

  Module Quote.

    (** Quote *)
    Record t := {
      instrument_id : N;
      bid : Bid.t;
      ask : Ask.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Bid.bounded (bid record) /\
      Ask.bounded (ask record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      Bid.encode (bid record) ++
      Ask.encode (ask record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match Bid.decode bytes with
          | None => None
          | Some (bid_value, bytes) =>
              match Ask.decode bytes with
              | None => None
              | Some (ask_value, bytes) =>
                  Some ({| instrument_id := instrument_id_value; bid := bid_value; ask := ask_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !Bid.encode_length, !Ask.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite Bid.decode_encode by exact bound_1.
      rewrite Ask.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Bid.eq_dec | apply Ask.eq_dec]. Defined.

  End Quote.

  Module MarketMakerCommand.

    (** Market Maker command request *)
    Record t := {
      instrument_id : N;
      action : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (action record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (action_value, bytes) =>
              Some ({| instrument_id := instrument_id_value; action := action_value |}, bytes)
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

  End MarketMakerCommand.

  Module MarketMakerCommandResponse.

    (** The response to the Market Maker command *)
    Record t := {
      ref_id : N;
      result_command_result : N;
      rejection_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ref_id record < 256 ^ N.of_nat 4)%N /\
      (result_command_result record < 256 ^ N.of_nat 1)%N /\
      (rejection_code record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (ref_id record) ++
      encode_uint 1 (result_command_result record) ++
      encode_uint 2 (rejection_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (ref_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (result_command_result_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (rejection_code_value, bytes) =>
                  Some ({| ref_id := ref_id_value; result_command_result := result_command_result_value; rejection_code := rejection_code_value |}, bytes)
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

  End MarketMakerCommandResponse.

  Module RequestForExecution.

    (** The information for the MM that one of the quotes has been crossed *)
    Record t := {
      instrument_id : N;
      reason_request_for_execution_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (reason_request_for_execution_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (reason_request_for_execution_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (reason_request_for_execution_reason_value, bytes) =>
              Some ({| instrument_id := instrument_id_value; reason_request_for_execution_reason := reason_request_for_execution_reason_value |}, bytes)
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

  End RequestForExecution.

  Module BidOfferUpdate.

    (** Message send during the IPO to the sell side or during the Tender Offer to the buy side *)
    Record t := {
      instrument_id : N;
      update_type : N;
      total_bid_size : N;
      total_offer_size : N;
      bid_orders : N;
      offer_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (update_type record < 256 ^ N.of_nat 1)%N /\
      (total_bid_size record < 256 ^ N.of_nat 8)%N /\
      (total_offer_size record < 256 ^ N.of_nat 8)%N /\
      (bid_orders record < 256 ^ N.of_nat 4)%N /\
      (offer_orders record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (update_type record) ++
      encode_uint 8 (total_bid_size record) ++
      encode_uint 8 (total_offer_size record) ++
      encode_uint 4 (bid_orders record) ++
      encode_uint 4 (offer_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (update_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (total_bid_size_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (total_offer_size_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_orders_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (offer_orders_value, bytes) =>
                              Some ({| instrument_id := instrument_id_value; update_type := update_type_value; total_bid_size := total_bid_size_value; total_offer_size := total_offer_size_value; bid_orders := bid_orders_value; offer_orders := offer_orders_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End BidOfferUpdate.

  Module Client5.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End Client5.

  Module ExecutingTrader6.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader6.

  Module InvestmentDecisionMaker5.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End InvestmentDecisionMaker5.

  Module MifidFields5.

    (** MifidFields *)
    Record t := {
      client : Client5.t;
      executing_trader : ExecutingTrader6.t;
      investment_decision_maker : InvestmentDecisionMaker5.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Client5.bounded (client record) /\
      ExecutingTrader6.bounded (executing_trader record) /\
      InvestmentDecisionMaker5.bounded (investment_decision_maker record).

    Definition encode (record : t) : list byte :=
      Client5.encode (client record) ++
      ExecutingTrader6.encode (executing_trader record) ++
      InvestmentDecisionMaker5.encode (investment_decision_maker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Client5.decode bytes with
      | None => None
      | Some (client_value, bytes) =>
          match ExecutingTrader6.decode bytes with
          | None => None
          | Some (executing_trader_value, bytes) =>
              match InvestmentDecisionMaker5.decode bytes with
              | None => None
              | Some (investment_decision_maker_value, bytes) =>
                  Some ({| client := client_value; executing_trader := executing_trader_value; investment_decision_maker := investment_decision_maker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Client5.encode_length, !ExecutingTrader6.encode_length, !InvestmentDecisionMaker5.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Client5.decode_encode by exact bound_0.
      rewrite ExecutingTrader6.decode_encode by exact bound_1.
      rewrite InvestmentDecisionMaker5.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Client5.eq_dec | apply ExecutingTrader6.eq_dec | apply InvestmentDecisionMaker5.eq_dec]. Defined.

  End MifidFields5.

  Module Client6.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End Client6.

  Module ExecutingTrader7.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader7.

  Module InvestmentDecisionMaker6.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End InvestmentDecisionMaker6.

  Module MifidFields6.

    (** MifidFields *)
    Record t := {
      client : Client6.t;
      executing_trader : ExecutingTrader7.t;
      investment_decision_maker : InvestmentDecisionMaker6.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Client6.bounded (client record) /\
      ExecutingTrader7.bounded (executing_trader record) /\
      InvestmentDecisionMaker6.bounded (investment_decision_maker record).

    Definition encode (record : t) : list byte :=
      Client6.encode (client record) ++
      ExecutingTrader7.encode (executing_trader record) ++
      InvestmentDecisionMaker6.encode (investment_decision_maker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Client6.decode bytes with
      | None => None
      | Some (client_value, bytes) =>
          match ExecutingTrader7.decode bytes with
          | None => None
          | Some (executing_trader_value, bytes) =>
              match InvestmentDecisionMaker6.decode bytes with
              | None => None
              | Some (investment_decision_maker_value, bytes) =>
                  Some ({| client := client_value; executing_trader := executing_trader_value; investment_decision_maker := investment_decision_maker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Client6.encode_length, !ExecutingTrader7.encode_length, !InvestmentDecisionMaker6.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Client6.decode_encode by exact bound_0.
      rewrite ExecutingTrader7.decode_encode by exact bound_1.
      rewrite InvestmentDecisionMaker6.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Client6.eq_dec | apply ExecutingTrader7.eq_dec | apply InvestmentDecisionMaker6.eq_dec]. Defined.

  End MifidFields6.

  Module Client7.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End Client7.

  Module ExecutingTrader8.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End ExecutingTrader8.

  Module InvestmentDecisionMaker7.

    (** MifidField *)
    Record t := {
      short_code : N;
      qualifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_code record < 256 ^ N.of_nat 4)%N /\
      (qualifier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (short_code record) ++
      encode_uint 1 (qualifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (short_code_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (qualifier_value, bytes) =>
              Some ({| short_code := short_code_value; qualifier := qualifier_value |}, bytes)
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

  End InvestmentDecisionMaker7.

  Module MifidFields7.

    (** MifidFields *)
    Record t := {
      client : Client7.t;
      executing_trader : ExecutingTrader8.t;
      investment_decision_maker : InvestmentDecisionMaker7.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Client7.bounded (client record) /\
      ExecutingTrader8.bounded (executing_trader record) /\
      InvestmentDecisionMaker7.bounded (investment_decision_maker record).

    Definition encode (record : t) : list byte :=
      Client7.encode (client record) ++
      ExecutingTrader8.encode (executing_trader record) ++
      InvestmentDecisionMaker7.encode (investment_decision_maker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Client7.decode bytes with
      | None => None
      | Some (client_value, bytes) =>
          match ExecutingTrader8.decode bytes with
          | None => None
          | Some (executing_trader_value, bytes) =>
              match InvestmentDecisionMaker7.decode bytes with
              | None => None
              | Some (investment_decision_maker_value, bytes) =>
                  Some ({| client := client_value; executing_trader := executing_trader_value; investment_decision_maker := investment_decision_maker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Client7.encode_length, !ExecutingTrader8.encode_length, !InvestmentDecisionMaker7.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Client7.decode_encode by exact bound_0.
      rewrite ExecutingTrader8.decode_encode by exact bound_1.
      rewrite InvestmentDecisionMaker7.decode_encode by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Client7.eq_dec | apply ExecutingTrader8.eq_dec | apply InvestmentDecisionMaker7.eq_dec]. Defined.

  End MifidFields7.

  Module TradeBust.

    (** Message used to inform about cancellation of previously accepted Trade *)
    Record t := {
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trade_id_value, bytes) =>
          Some ({| trade_id := trade_id_value |}, bytes)
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

  End TradeBust.

End WseOrderEntryV17620.
