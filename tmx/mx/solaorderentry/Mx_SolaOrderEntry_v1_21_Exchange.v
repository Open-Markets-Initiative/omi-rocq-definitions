From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Sola Order Entry

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
      - a run counted by a field
  *)

Module MxSolaOrderEntryV121Exchange.

  Module ConnectionAcknowledgement.

    Record t := {
      current_session_id : list byte;
      last_user_sequence_id_received : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (current_session_id record) = 4 /\
      Datatypes.length (last_user_sequence_id_received record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (current_session_id record) ++
      encode_bytes 8 (last_user_sequence_id_received record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (current_session_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (last_user_sequence_id_received_value, bytes) =>
              Some ({| current_session_id := current_session_id_value; last_user_sequence_id_received := last_user_sequence_id_received_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConnectionAcknowledgement.

  Module DisconnectionInstructionAcknowledgement.

    Record t := {
      current_session_id : list byte;
      last_user_sequence_id_received : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (current_session_id record) = 4 /\
      Datatypes.length (last_user_sequence_id_received record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (current_session_id record) ++
      encode_bytes 8 (last_user_sequence_id_received record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (current_session_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (last_user_sequence_id_received_value, bytes) =>
              Some ({| current_session_id := current_session_id_value; last_user_sequence_id_received := last_user_sequence_id_received_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DisconnectionInstructionAcknowledgement.

  Module HeartbeatQuestion.

    Record t := {
      user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period : list byte;
      last_exchange_message_id_sent_to_participant : list byte;
      trading_engine_timestamp_local_hhmmss : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period record) = 8 /\
      Datatypes.length (last_exchange_message_id_sent_to_participant record) = 6 /\
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period record) ++
      encode_bytes 6 (last_exchange_message_id_sent_to_participant record) ++
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (last_exchange_message_id_sent_to_participant_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
                  Some ({| user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period := user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period_value; last_exchange_message_id_sent_to_participant := last_exchange_message_id_sent_to_participant_value; trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HeartbeatQuestion.

  Module OutOfSequence.

    Record t := {
      received_user_sequence_id : list byte;
      expected_last_user_sequence_id : list byte;
      user_message_timestamp_local_hhmmss : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (received_user_sequence_id record) = 8 /\
      Datatypes.length (expected_last_user_sequence_id record) = 8 /\
      Datatypes.length (user_message_timestamp_local_hhmmss record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (received_user_sequence_id record) ++
      encode_bytes 8 (expected_last_user_sequence_id record) ++
      encode_bytes 6 (user_message_timestamp_local_hhmmss record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (received_user_sequence_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (expected_last_user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (user_message_timestamp_local_hhmmss_value, bytes) =>
                  Some ({| received_user_sequence_id := received_user_sequence_id_value; expected_last_user_sequence_id := expected_last_user_sequence_id_value; user_message_timestamp_local_hhmmss := user_message_timestamp_local_hhmmss_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutOfSequence.

  Module TechnicalErrorNotice.

    Record t := {
      received_message_type : list byte;
      preceding_user_sequence_id_received_zeroes_if_none : list byte;
      error_code : list byte;
      error_position : list byte;
      error_message : list byte;
      start_of_message_in_error : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (received_message_type record) = 2 /\
      Datatypes.length (preceding_user_sequence_id_received_zeroes_if_none record) = 8 /\
      Datatypes.length (error_code record) = 4 /\
      Datatypes.length (error_position record) = 4 /\
      Datatypes.length (error_message record) = 100 /\
      Datatypes.length (start_of_message_in_error record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (received_message_type record) ++
      encode_bytes 8 (preceding_user_sequence_id_received_zeroes_if_none record) ++
      encode_bytes 4 (error_code record) ++
      encode_bytes 4 (error_position record) ++
      encode_bytes 100 (error_message record) ++
      encode_bytes 100 (start_of_message_in_error record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (received_message_type_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (preceding_user_sequence_id_received_zeroes_if_none_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (error_code_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (error_position_value, bytes) =>
                      match decode_bytes 100 bytes with
                      | None => None
                      | Some (error_message_value, bytes) =>
                          match decode_bytes 100 bytes with
                          | None => None
                          | Some (start_of_message_in_error_value, bytes) =>
                              Some ({| received_message_type := received_message_type_value; preceding_user_sequence_id_received_zeroes_if_none := preceding_user_sequence_id_received_zeroes_if_none_value; error_code := error_code_value; error_position := error_position_value; error_message := error_message_value; start_of_message_in_error := start_of_message_in_error_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 218.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TechnicalErrorNotice.

  Module DisconnectionAcknowledgement.

    Record t := {
      current_session_id : list byte;
      last_user_sequence_id_received : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (current_session_id record) = 4 /\
      Datatypes.length (last_user_sequence_id_received record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (current_session_id record) ++
      encode_bytes 8 (last_user_sequence_id_received record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (current_session_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (last_user_sequence_id_received_value, bytes) =>
              Some ({| current_session_id := current_session_id_value; last_user_sequence_id_received := last_user_sequence_id_received_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DisconnectionAcknowledgement.

  Module EndOfTransmission.

    Record t := {
      ended_session_id : list byte;
      last_user_sequence_id_received_if_no_business_message_has_been_received_on_this_connection_this_field_is_equal_to_zeroes : list byte;
      trading_engine_timestamp_local_hhmmss : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ended_session_id record) = 4 /\
      Datatypes.length (last_user_sequence_id_received_if_no_business_message_has_been_received_on_this_connection_this_field_is_equal_to_zeroes record) = 8 /\
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (ended_session_id record) ++
      encode_bytes 8 (last_user_sequence_id_received_if_no_business_message_has_been_received_on_this_connection_this_field_is_equal_to_zeroes record) ++
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (ended_session_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (last_user_sequence_id_received_if_no_business_message_has_been_received_on_this_connection_this_field_is_equal_to_zeroes_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
                  Some ({| ended_session_id := ended_session_id_value; last_user_sequence_id_received_if_no_business_message_has_been_received_on_this_connection_this_field_is_equal_to_zeroes := last_user_sequence_id_received_if_no_business_message_has_been_received_on_this_connection_this_field_is_equal_to_zeroes_value; trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfTransmission.

  Module OutgoingMessagesHeader.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader.

  Module ClearingData.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData.

  Module OwnerData.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData.

  Module OrderReply.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity_remaining : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData.t;
      owner_data : OwnerData.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_remaining record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData.bounded (clearing_data record) /\
      OwnerData.bounded (owner_data record).

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_remaining record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData.encode (clearing_data record) ++
      OwnerData.encode (owner_data record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (status_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (verb_side_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (quantity_remaining_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (assigned_price_value, bytes) =>
                                          match ClearingData.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity_remaining := quantity_remaining_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 134.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader.encode_length, !encode_bytes_length, !ClearingData.encode_length, !OwnerData.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData.decode_encode by exact bound_9.
      rewrite OwnerData.decode_encode by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader.eq_dec | apply ClearingData.eq_dec | apply OwnerData.eq_dec]. Defined.

  End OrderReply.

  Module OutgoingMessagesHeader2.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader2.

  Module ErrorNotice.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader2.t;
      error_code : list byte;
      error_description : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader2.bounded (outgoing_messages_header record) /\
      Datatypes.length (error_code record) = 4 /\
      Datatypes.length (error_description record) = 100.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader2.encode (outgoing_messages_header record) ++
      encode_bytes 4 (error_code record) ++
      encode_bytes 100 (error_description record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader2.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (error_code_value, bytes) =>
              match decode_bytes 100 bytes with
              | None => None
              | Some (error_description_value, bytes) =>
                  Some ({| outgoing_messages_header := outgoing_messages_header_value; error_code := error_code_value; error_description := error_description_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 126.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader2.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader2.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader2.eq_dec]. Defined.

  End ErrorNotice.

  Module OutgoingMessagesHeader3.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader3.

  Module BulkQuoteDataAcknowledgement.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader3.t;
      group : list byte;
      trader_id : list byte;
      quote_id_identifies_traders_quote_on_this_group : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader3.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (quote_id_identifies_traders_quote_on_this_group record) = 8.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader3.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (quote_id_identifies_traders_quote_on_this_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader3.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (quote_id_identifies_traders_quote_on_this_group_value, bytes) =>
                      Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; trader_id := trader_id_value; quote_id_identifies_traders_quote_on_this_group := quote_id_identifies_traders_quote_on_this_group_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader3.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader3.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader3.eq_dec]. Defined.

  End BulkQuoteDataAcknowledgement.

  Module OutgoingMessagesHeader4.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader4.

  Module ClearingData2.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData2.

  Module OwnerData2.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData2.

  Module OrderAcknowledgement.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader4.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData2.t;
      owner_data : OwnerData2.t;
      original_order_id : list byte;
      filler_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader4.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData2.bounded (clearing_data record) /\
      OwnerData2.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader4.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData2.encode (clearing_data record) ++
      OwnerData2.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_uint 6 (filler_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader4.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (status_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (verb_side_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (quantity_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (assigned_price_value, bytes) =>
                                          match ClearingData2.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData2.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (original_order_id_value, bytes) =>
                                                      match decode_uint 6 bytes with
                                                      | None => None
                                                      | Some (filler_6_value, bytes) =>
                                                          Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; filler_6 := filler_6_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 148.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader4.encode_length, !encode_bytes_length, !ClearingData2.encode_length, !OwnerData2.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader4.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData2.decode_encode by exact bound_9.
      rewrite OwnerData2.decode_encode by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader4.eq_dec | apply ClearingData2.eq_dec | apply OwnerData2.eq_dec]. Defined.

  End OrderAcknowledgement.

  Module OutgoingMessagesHeader5.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader5.

  Module GlobalCancellationConfirmation.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader5.t;
      group : list byte;
      trader_id : list byte;
      type_of_cancellation_only_q_quotes_only_can_be_returned : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader5.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (type_of_cancellation_only_q_quotes_only_can_be_returned record) = 1.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader5.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 1 (type_of_cancellation_only_q_quotes_only_can_be_returned record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader5.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (type_of_cancellation_only_q_quotes_only_can_be_returned_value, bytes) =>
                      Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; trader_id := trader_id_value; type_of_cancellation_only_q_quotes_only_can_be_returned := type_of_cancellation_only_q_quotes_only_can_be_returned_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader5.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader5.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader5.eq_dec]. Defined.

  End GlobalCancellationConfirmation.

  Module OutgoingMessagesHeader6.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader6.

  Module ClearingData3.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData3.

  Module OwnerData3.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData3.

  Module OrderModificationAcknowledgement.

    (** This message is sent by the Exchange to acknowledge an OM: Order Modification message. This message has the same format as the KE: Order Acknowledgement (the extensive list of fields is only described there), KZ: Order Cancellation Acknowledgement and NZ: Order Cancellation Notice (by MOD or System) messages. *)
    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader6.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData3.t;
      owner_data : OwnerData3.t;
      original_order_id : list byte;
      filler_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader6.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData3.bounded (clearing_data record) /\
      OwnerData3.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader6.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData3.encode (clearing_data record) ++
      OwnerData3.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_uint 6 (filler_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader6.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (status_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (verb_side_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (quantity_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (assigned_price_value, bytes) =>
                                          match ClearingData3.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData3.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (original_order_id_value, bytes) =>
                                                      match decode_uint 6 bytes with
                                                      | None => None
                                                      | Some (filler_6_value, bytes) =>
                                                          Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; filler_6 := filler_6_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 148.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader6.encode_length, !encode_bytes_length, !ClearingData3.encode_length, !OwnerData3.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader6.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData3.decode_encode by exact bound_9.
      rewrite OwnerData3.decode_encode by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader6.eq_dec | apply ClearingData3.eq_dec | apply OwnerData3.eq_dec]. Defined.

  End OrderModificationAcknowledgement.

  Module OutgoingMessagesHeader7.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader7.

  Module OutgoingMessagesHeader8.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader8.

  Module StandardAcknowledgement.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader8.t;
      trader_id : list byte;
      original_message_type_af_gz_ml_ox_or_rq : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader8.bounded (outgoing_messages_header record) /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (original_message_type_af_gz_ml_ox_or_rq record) = 2.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader8.encode (outgoing_messages_header record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 2 (original_message_type_af_gz_ml_ox_or_rq record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader8.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (original_message_type_af_gz_ml_ox_or_rq_value, bytes) =>
                  Some ({| outgoing_messages_header := outgoing_messages_header_value; trader_id := trader_id_value; original_message_type_af_gz_ml_ox_or_rq := original_message_type_af_gz_ml_ox_or_rq_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader8.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader8.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader8.eq_dec]. Defined.

  End StandardAcknowledgement.

  Module OutgoingMessagesHeader9.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader9.

  Module ClearingData4.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData4.

  Module OwnerData4.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData4.

  Module OrderCancellationAcknowledgement.

    (** This message is to acknowledge an XE: Order Cancellation message. This message has the same number of bytes and format as the KE: Order Acknowledgement (the extensive list of fields is only described there), the KM: Order Modification Acknowledgement and the NZ: Order Cancellation Notice (by MOD or System) messages. *)
    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader9.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData4.t;
      owner_data : OwnerData4.t;
      original_order_id : list byte;
      filler_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader9.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData4.bounded (clearing_data record) /\
      OwnerData4.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader9.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData4.encode (clearing_data record) ++
      OwnerData4.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_uint 6 (filler_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader9.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (status_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (verb_side_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (quantity_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (assigned_price_value, bytes) =>
                                          match ClearingData4.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData4.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (original_order_id_value, bytes) =>
                                                      match decode_uint 6 bytes with
                                                      | None => None
                                                      | Some (filler_6_value, bytes) =>
                                                          Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; filler_6 := filler_6_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 148.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader9.encode_length, !encode_bytes_length, !ClearingData4.encode_length, !OwnerData4.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader9.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData4.decode_encode by exact bound_9.
      rewrite OwnerData4.decode_encode by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader9.eq_dec | apply ClearingData4.eq_dec | apply OwnerData4.eq_dec]. Defined.

  End OrderCancellationAcknowledgement.

  Module OutgoingMessagesHeader10.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader10.

  Module OutgoingMessagesHeader11.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader11.

  Module OutgoingMessagesHeader12.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader12.

  Module OutgoingMessagesHeader13.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader13.

  Module OutgoingMessagesHeader14.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader14.

  Module GroupStateChange.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader14.t;
      group : list byte;
      group_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader14.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (group_state record) = 1.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader14.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 1 (group_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader14.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (group_state_value, bytes) =>
                  Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; group_state := group_state_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader14.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader14.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader14.eq_dec]. Defined.

  End GroupStateChange.

  Module OutgoingMessagesHeader15.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader15.

  Module InstrumentStateChange.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader15.t;
      group : list byte;
      instrument : list byte;
      instrument_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader15.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (instrument_state record) = 1.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader15.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 1 (instrument_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader15.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (instrument_state_value, bytes) =>
                      Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; instrument_state := instrument_state_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader15.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader15.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader15.eq_dec]. Defined.

  End InstrumentStateChange.

  Module OutgoingMessagesHeader16.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader16.

  Module ClearingData5.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData5.

  Module OwnerData5.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData5.

  Module LegExecutionNotice.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader16.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      reference_id_order_id_or_quote_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      trading_engine_timestamp_of_the_trade_local_hhmmss : list byte;
      clearing_data : ClearingData5.t;
      owner_data : OwnerData5.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      filler_6 : N;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
      strategy_group : list byte;
      strategy_instrument_id : list byte;
      strategy_verb_side : list byte;
      strategy_trade_number : list byte;
      leg_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader16.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id_order_id_or_quote_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (trading_engine_timestamp_of_the_trade_local_hhmmss record) = 6 /\
      ClearingData5.bounded (clearing_data record) /\
      OwnerData5.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4 /\
      Datatypes.length (strategy_group record) = 2 /\
      Datatypes.length (strategy_instrument_id record) = 4 /\
      Datatypes.length (strategy_verb_side record) = 1 /\
      Datatypes.length (strategy_trade_number record) = 8 /\
      Datatypes.length (leg_number record) = 2.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader16.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id_order_id_or_quote_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (trading_engine_timestamp_of_the_trade_local_hhmmss record) ++
      ClearingData5.encode (clearing_data record) ++
      OwnerData5.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 6 (filler_6 record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record) ++
      encode_bytes 2 (strategy_group record) ++
      encode_bytes 4 (strategy_instrument_id record) ++
      encode_bytes 1 (strategy_verb_side record) ++
      encode_bytes 8 (strategy_trade_number record) ++
      encode_bytes 2 (leg_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader16.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (reference_id_order_id_or_quote_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (verb_side_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (quantity_traded_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (trading_engine_timestamp_of_the_trade_local_hhmmss_value, bytes) =>
                                          match ClearingData5.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData5.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (special_trade_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (price_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_type_value, bytes) =>
                                                              match decode_uint 6 bytes with
                                                              | None => None
                                                              | Some (filler_6_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (trade_number_value, bytes) =>
                                                                      match decode_bytes 50 bytes with
                                                                      | None => None
                                                                      | Some (trade_memo_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (original_reference_id_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (id_code_for_the_counterpart_participant_value, bytes) =>
                                                                                  match decode_bytes 2 bytes with
                                                                                  | None => None
                                                                                  | Some (strategy_group_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (strategy_instrument_id_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (strategy_verb_side_value, bytes) =>
                                                                                              match decode_bytes 8 bytes with
                                                                                              | None => None
                                                                                              | Some (strategy_trade_number_value, bytes) =>
                                                                                                  match decode_bytes 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (leg_number_value, bytes) =>
                                                                                                      Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; reference_id_order_id_or_quote_id := reference_id_order_id_or_quote_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; trading_engine_timestamp_of_the_trade_local_hhmmss := trading_engine_timestamp_of_the_trade_local_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; filler_6 := filler_6_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value; strategy_group := strategy_group_value; strategy_instrument_id := strategy_instrument_id_value; strategy_verb_side := strategy_verb_side_value; strategy_trade_number := strategy_trade_number_value; leg_number := leg_number_value |}, bytes)
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 235.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader16.encode_length, !encode_bytes_length, !ClearingData5.encode_length, !OwnerData5.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 bound_23]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader16.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData5.decode_encode by exact bound_9.
      rewrite OwnerData5.decode_encode by exact bound_10.
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
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader16.eq_dec | apply ClearingData5.eq_dec | apply OwnerData5.eq_dec]. Defined.

  End LegExecutionNotice.

  Module OutgoingMessagesHeader17.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader17.

  Module CounterpartOwnerData.

    (** Owner Data of the counterpart, which NO: Overstepped Order or Quote Notice carries. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End CounterpartOwnerData.

  Module OversteppedOrderOrQuoteNotice.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader17.t;
      group : list byte;
      instrument : list byte;
      verb : list byte;
      order_type : list byte;
      trader_id : list byte;
      order_id : list byte;
      counterpart_trader_id : list byte;
      counterpart_order_id : list byte;
      counterpart_owner_data : CounterpartOwnerData.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader17.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (verb record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (counterpart_trader_id record) = 8 /\
      Datatypes.length (counterpart_order_id record) = 8 /\
      CounterpartOwnerData.bounded (counterpart_owner_data record).

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader17.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 1 (verb record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 8 (counterpart_trader_id record) ++
      encode_bytes 8 (counterpart_order_id record) ++
      CounterpartOwnerData.encode (counterpart_owner_data record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader17.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (verb_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_type_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (trader_id_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (order_id_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (counterpart_trader_id_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (counterpart_order_id_value, bytes) =>
                                          match CounterpartOwnerData.decode bytes with
                                          | None => None
                                          | Some (counterpart_owner_data_value, bytes) =>
                                              Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; verb := verb_value; order_type := order_type_value; trader_id := trader_id_value; order_id := order_id_value; counterpart_trader_id := counterpart_trader_id_value; counterpart_order_id := counterpart_order_id_value; counterpart_owner_data := counterpart_owner_data_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 112.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader17.encode_length, !encode_bytes_length, !CounterpartOwnerData.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader17.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite CounterpartOwnerData.decode_encode by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader17.eq_dec | apply CounterpartOwnerData.eq_dec]. Defined.

  End OversteppedOrderOrQuoteNotice.

  Module OutgoingMessagesHeader18.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader18.

  Module CancellationOfAllQuotesNotice.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader18.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader18.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader18.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader18.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cancel_reason_value, bytes) =>
                          Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; cancel_reason := cancel_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader18.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader18.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader18.eq_dec]. Defined.

  End CancellationOfAllQuotesNotice.

  Module OutgoingMessagesHeader19.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader19.

  Module ClearingData6.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData6.

  Module OwnerData6.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData6.

  Module ExecutionNotice.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader19.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      reference_id_order_id_or_quote_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      trading_engine_timestamp_of_the_trade_local_hhmmss : list byte;
      clearing_data : ClearingData6.t;
      owner_data : OwnerData6.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      filler_6 : N;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader19.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id_order_id_or_quote_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (trading_engine_timestamp_of_the_trade_local_hhmmss record) = 6 /\
      ClearingData6.bounded (clearing_data record) /\
      OwnerData6.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader19.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id_order_id_or_quote_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (trading_engine_timestamp_of_the_trade_local_hhmmss record) ++
      ClearingData6.encode (clearing_data record) ++
      OwnerData6.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 6 (filler_6 record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader19.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (reference_id_order_id_or_quote_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (verb_side_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (quantity_traded_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (trading_engine_timestamp_of_the_trade_local_hhmmss_value, bytes) =>
                                          match ClearingData6.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData6.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (special_trade_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (price_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_type_value, bytes) =>
                                                              match decode_uint 6 bytes with
                                                              | None => None
                                                              | Some (filler_6_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (trade_number_value, bytes) =>
                                                                      match decode_bytes 50 bytes with
                                                                      | None => None
                                                                      | Some (trade_memo_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (original_reference_id_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (id_code_for_the_counterpart_participant_value, bytes) =>
                                                                                  Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; reference_id_order_id_or_quote_id := reference_id_order_id_or_quote_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; trading_engine_timestamp_of_the_trade_local_hhmmss := trading_engine_timestamp_of_the_trade_local_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; filler_6 := filler_6_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 218.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader19.encode_length, !encode_bytes_length, !ClearingData6.encode_length, !OwnerData6.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader19.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData6.decode_encode by exact bound_9.
      rewrite OwnerData6.decode_encode by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader19.eq_dec | apply ClearingData6.eq_dec | apply OwnerData6.eq_dec]. Defined.

  End ExecutionNotice.

  Module OutgoingMessagesHeader20.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader20.

  Module ClearingData7.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData7.

  Module OwnerData7.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData7.

  Module ExecutionCancellationNotice.

    (** This message is sent by the Exchange to report the execution of a trade cancellation by the MOD. This message has the same number of bytes and format as the NT: SAIL Execution Notice messages. *)
    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader20.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      reference_id_order_id_or_quote_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      trading_engine_timestamp_of_the_trade_local_hhmmss : list byte;
      clearing_data : ClearingData7.t;
      owner_data : OwnerData7.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      filler_6 : N;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader20.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id_order_id_or_quote_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (trading_engine_timestamp_of_the_trade_local_hhmmss record) = 6 /\
      ClearingData7.bounded (clearing_data record) /\
      OwnerData7.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader20.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id_order_id_or_quote_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (trading_engine_timestamp_of_the_trade_local_hhmmss record) ++
      ClearingData7.encode (clearing_data record) ++
      OwnerData7.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 6 (filler_6 record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader20.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (reference_id_order_id_or_quote_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (verb_side_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (quantity_traded_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (trading_engine_timestamp_of_the_trade_local_hhmmss_value, bytes) =>
                                          match ClearingData7.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData7.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (special_trade_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (price_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_type_value, bytes) =>
                                                              match decode_uint 6 bytes with
                                                              | None => None
                                                              | Some (filler_6_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (trade_number_value, bytes) =>
                                                                      match decode_bytes 50 bytes with
                                                                      | None => None
                                                                      | Some (trade_memo_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (original_reference_id_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (id_code_for_the_counterpart_participant_value, bytes) =>
                                                                                  Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; reference_id_order_id_or_quote_id := reference_id_order_id_or_quote_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; trading_engine_timestamp_of_the_trade_local_hhmmss := trading_engine_timestamp_of_the_trade_local_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; filler_6 := filler_6_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 218.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader20.encode_length, !encode_bytes_length, !ClearingData7.encode_length, !OwnerData7.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader20.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData7.decode_encode by exact bound_9.
      rewrite OwnerData7.decode_encode by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader20.eq_dec | apply ClearingData7.eq_dec | apply OwnerData7.eq_dec]. Defined.

  End ExecutionCancellationNotice.

  Module OutgoingMessagesHeader21.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader21.

  Module ClearingData8.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData8.

  Module OwnerData8.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData8.

  Module LegExecutionCancellationNotice.

    (** This message is sent by the Exchange to report the execution of a cancellation by the MOD for a leg of the strategy trade. This message has the same number of bytes and format as the NL: Leg Execution Notice message. *)
    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader21.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      reference_id_order_id_or_quote_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      trading_engine_timestamp_of_the_trade_local_hhmmss : list byte;
      clearing_data : ClearingData8.t;
      owner_data : OwnerData8.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      filler_6 : N;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
      strategy_group : list byte;
      strategy_instrument_id : list byte;
      strategy_verb_side : list byte;
      strategy_trade_number : list byte;
      leg_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader21.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id_order_id_or_quote_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (trading_engine_timestamp_of_the_trade_local_hhmmss record) = 6 /\
      ClearingData8.bounded (clearing_data record) /\
      OwnerData8.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4 /\
      Datatypes.length (strategy_group record) = 2 /\
      Datatypes.length (strategy_instrument_id record) = 4 /\
      Datatypes.length (strategy_verb_side record) = 1 /\
      Datatypes.length (strategy_trade_number record) = 8 /\
      Datatypes.length (leg_number record) = 2.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader21.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id_order_id_or_quote_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (trading_engine_timestamp_of_the_trade_local_hhmmss record) ++
      ClearingData8.encode (clearing_data record) ++
      OwnerData8.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 6 (filler_6 record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record) ++
      encode_bytes 2 (strategy_group record) ++
      encode_bytes 4 (strategy_instrument_id record) ++
      encode_bytes 1 (strategy_verb_side record) ++
      encode_bytes 8 (strategy_trade_number record) ++
      encode_bytes 2 (leg_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader21.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (reference_id_order_id_or_quote_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (verb_side_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (quantity_traded_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (trading_engine_timestamp_of_the_trade_local_hhmmss_value, bytes) =>
                                          match ClearingData8.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData8.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (special_trade_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (price_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_type_value, bytes) =>
                                                              match decode_uint 6 bytes with
                                                              | None => None
                                                              | Some (filler_6_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (trade_number_value, bytes) =>
                                                                      match decode_bytes 50 bytes with
                                                                      | None => None
                                                                      | Some (trade_memo_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (original_reference_id_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (id_code_for_the_counterpart_participant_value, bytes) =>
                                                                                  match decode_bytes 2 bytes with
                                                                                  | None => None
                                                                                  | Some (strategy_group_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (strategy_instrument_id_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (strategy_verb_side_value, bytes) =>
                                                                                              match decode_bytes 8 bytes with
                                                                                              | None => None
                                                                                              | Some (strategy_trade_number_value, bytes) =>
                                                                                                  match decode_bytes 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (leg_number_value, bytes) =>
                                                                                                      Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; reference_id_order_id_or_quote_id := reference_id_order_id_or_quote_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; trading_engine_timestamp_of_the_trade_local_hhmmss := trading_engine_timestamp_of_the_trade_local_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; filler_6 := filler_6_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value; strategy_group := strategy_group_value; strategy_instrument_id := strategy_instrument_id_value; strategy_verb_side := strategy_verb_side_value; strategy_trade_number := strategy_trade_number_value; leg_number := leg_number_value |}, bytes)
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 235.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader21.encode_length, !encode_bytes_length, !ClearingData8.encode_length, !OwnerData8.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 bound_23]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader21.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData8.decode_encode by exact bound_9.
      rewrite OwnerData8.decode_encode by exact bound_10.
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
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader21.eq_dec | apply ClearingData8.eq_dec | apply OwnerData8.eq_dec]. Defined.

  End LegExecutionCancellationNotice.

  Module OutgoingMessagesHeader22.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader22.

  Module ClearingData9.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      filler_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      (filler_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_uint 5 (filler_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (clearing_instruction_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (account_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_close_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (hedge_spec_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (filler_5_value, bytes) =>
                          Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; filler_5 := filler_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearingData9.

  Module OwnerData9.

    (** The guide states this field once, as Owner Data, for every message that carries it. *)
    Record t := {
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 50 bytes with
      | None => None
      | Some (memo_value, bytes) =>
          Some ({| memo := memo_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End OwnerData9.

  Module OrderCancellationNoticeByModOrSystem.

    (** This triggered message is sent by the Exchange to report the cancellation of an order by the MOD or by the System. This message has the same number of bytes and format as the KE: Order Acknowledgement, KM: Order Modification Acknowledgement and KZ: Order Cancellation Acknowledgement messages. *)
    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader22.t;
      group : list byte;
      instrument : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData9.t;
      owner_data : OwnerData9.t;
      original_order_id : list byte;
      filler_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader22.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData9.bounded (clearing_data record) /\
      OwnerData9.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader22.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData9.encode (clearing_data record) ++
      OwnerData9.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_uint 6 (filler_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader22.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (status_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (verb_side_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (quantity_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (assigned_price_value, bytes) =>
                                          match ClearingData9.decode bytes with
                                          | None => None
                                          | Some (clearing_data_value, bytes) =>
                                              match OwnerData9.decode bytes with
                                              | None => None
                                              | Some (owner_data_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (original_order_id_value, bytes) =>
                                                      match decode_uint 6 bytes with
                                                      | None => None
                                                      | Some (filler_6_value, bytes) =>
                                                          Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; filler_6 := filler_6_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 148.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader22.encode_length, !encode_bytes_length, !ClearingData9.encode_length, !OwnerData9.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader22.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ClearingData9.decode_encode by exact bound_9.
      rewrite OwnerData9.decode_encode by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader22.eq_dec | apply ClearingData9.eq_dec | apply OwnerData9.eq_dec]. Defined.

  End OrderCancellationNoticeByModOrSystem.

  Module OutgoingMessagesHeader23.

    (** The guide states these fields once, as the Outgoing Messages Header, for every business message the Exchange sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      trading_engine_timestamp_local_hhmmss : list byte;
      user_sequence_id : list byte;
      exchange_message_id : list byte;
      gap_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (user_sequence_id record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_id record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trading_engine_timestamp_local_hhmmss record) ++
      encode_bytes 8 (user_sequence_id record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trading_engine_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (exchange_message_id_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (gap_sequence_id_value, bytes) =>
                      Some ({| trading_engine_timestamp_local_hhmmss := trading_engine_timestamp_local_hhmmss_value; user_sequence_id := user_sequence_id_value; exchange_message_id := exchange_message_id_value; gap_sequence_id := gap_sequence_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutgoingMessagesHeader23.

  Module RequestForQuoteWithSideAcknowledgement.

    Record t := {
      outgoing_messages_header : OutgoingMessagesHeader23.t;
      group : list byte;
      instrument : list byte;
      quantity : list byte;
      market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutgoingMessagesHeader23.bounded (outgoing_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (market_side record) = 1.

    Definition encode (record : t) : list byte :=
      OutgoingMessagesHeader23.encode (outgoing_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 1 (market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutgoingMessagesHeader23.decode bytes with
      | None => None
      | Some (outgoing_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (market_side_value, bytes) =>
                          Some ({| outgoing_messages_header := outgoing_messages_header_value; group := group_value; instrument := instrument_value; quantity := quantity_value; market_side := market_side_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutgoingMessagesHeader23.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutgoingMessagesHeader23.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutgoingMessagesHeader23.eq_dec]. Defined.

  End RequestForQuoteWithSideAcknowledgement.

End MxSolaOrderEntryV121Exchange.
