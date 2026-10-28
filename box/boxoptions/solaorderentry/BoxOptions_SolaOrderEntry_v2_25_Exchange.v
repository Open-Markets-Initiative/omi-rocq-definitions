From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Box Options Market Sola Order Entry

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

Module BoxOptionsSolaOrderEntryV225Exchange.

  Module OutgoingHeader.

    (** The header on all outgoing exchange messages *)
    Record t := {
      message_type : list byte;
      message_timestamp : list byte;
      user_sequence_i_d : list byte;
      exchange_message_id : list byte;
      gap_sequence_i_d : list byte;
      system_sequence_i_d : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_type record) = 2 /\
      Datatypes.length (message_timestamp record) = 6 /\
      Datatypes.length (user_sequence_i_d record) = 8 /\
      Datatypes.length (exchange_message_id record) = 6 /\
      Datatypes.length (gap_sequence_i_d record) = 2 /\
      Datatypes.length (system_sequence_i_d record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (message_type record) ++
      encode_bytes 6 (message_timestamp record) ++
      encode_bytes 8 (user_sequence_i_d record) ++
      encode_bytes 6 (exchange_message_id record) ++
      encode_bytes 2 (gap_sequence_i_d record) ++
      encode_bytes 6 (system_sequence_i_d record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (message_timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_i_d_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (exchange_message_id_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (gap_sequence_i_d_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (system_sequence_i_d_value, bytes) =>
                              Some ({| message_type := message_type_value; message_timestamp := message_timestamp_value; user_sequence_i_d := user_sequence_i_d_value; exchange_message_id := exchange_message_id_value; gap_sequence_i_d := gap_sequence_i_d_value; system_sequence_i_d := system_sequence_i_d_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End OutgoingHeader.

  Module HeartbeatQuestion.

    Record t := {
      first_user_sequence_i_d : list byte;
      last_exchange_message_id_sent_to_participant : list byte;
      time_local : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (first_user_sequence_i_d record) = 8 /\
      Datatypes.length (last_exchange_message_id_sent_to_participant record) = 6 /\
      Datatypes.length (time_local record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (first_user_sequence_i_d record) ++
      encode_bytes 6 (last_exchange_message_id_sent_to_participant record) ++
      encode_bytes 6 (time_local record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (first_user_sequence_i_d_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (last_exchange_message_id_sent_to_participant_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_local_value, bytes) =>
                  Some ({| first_user_sequence_i_d := first_user_sequence_i_d_value; last_exchange_message_id_sent_to_participant := last_exchange_message_id_sent_to_participant_value; time_local := time_local_value |}, bytes)
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
      message_time_local : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (received_user_sequence_id record) = 8 /\
      Datatypes.length (expected_last_user_sequence_id record) = 8 /\
      Datatypes.length (message_time_local record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (received_user_sequence_id record) ++
      encode_bytes 8 (expected_last_user_sequence_id record) ++
      encode_bytes 6 (message_time_local record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (received_user_sequence_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (expected_last_user_sequence_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (message_time_local_value, bytes) =>
                  Some ({| received_user_sequence_id := received_user_sequence_id_value; expected_last_user_sequence_id := expected_last_user_sequence_id_value; message_time_local := message_time_local_value |}, bytes)
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
      preceding_user_sequence_i_d_received : list byte;
      error_code : list byte;
      error_position : list byte;
      error_message : list byte;
      start_of_message_in_error : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (received_message_type record) = 2 /\
      Datatypes.length (preceding_user_sequence_i_d_received record) = 8 /\
      Datatypes.length (error_code record) = 4 /\
      Datatypes.length (error_position record) = 4 /\
      Datatypes.length (error_message record) = 100 /\
      Datatypes.length (start_of_message_in_error record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (received_message_type record) ++
      encode_bytes 8 (preceding_user_sequence_i_d_received record) ++
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
          | Some (preceding_user_sequence_i_d_received_value, bytes) =>
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
                              Some ({| received_message_type := received_message_type_value; preceding_user_sequence_i_d_received := preceding_user_sequence_i_d_received_value; error_code := error_code_value; error_position := error_position_value; error_message := error_message_value; start_of_message_in_error := start_of_message_in_error_value |}, bytes)
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

  Module ConnectionAcknowledgement.

    (** Stated by the guide as having the same number of bytes and format as TM, whose fields are written out here. *)
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

  Module DisconnectionAcknowledgement.

    (** Stated by the guide as having the same number of bytes and format as TM, whose fields are written out here. *)
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
      last_user_sequence_id_received : list byte;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ended_session_id record) = 4 /\
      Datatypes.length (last_user_sequence_id_received record) = 8 /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (ended_session_id record) ++
      encode_bytes 8 (last_user_sequence_id_received record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (ended_session_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (last_user_sequence_id_received_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_value, bytes) =>
                  Some ({| ended_session_id := ended_session_id_value; last_user_sequence_id_received := last_user_sequence_id_received_value; time := time_value |}, bytes)
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

  Module ErrorNotice.

    Record t := {
      error_code : list byte;
      error_description : list byte;
      group : list byte;
      instrument_optional : list byte;
      order_id_error_notice : list byte;
      auction_i_d_optional : list byte;
      original_message_type : list byte;
      error_detail : list byte;
      client_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (error_code record) = 4 /\
      Datatypes.length (error_description record) = 100 /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (order_id_error_notice record) = 20 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (original_message_type record) = 2 /\
      Datatypes.length (error_detail record) = 200 /\
      Datatypes.length (client_order_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (error_code record) ++
      encode_bytes 100 (error_description record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 20 (order_id_error_notice record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 2 (original_message_type record) ++
      encode_bytes 200 (error_detail record) ++
      encode_bytes 20 (client_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (error_code_value, bytes) =>
          match decode_bytes 100 bytes with
          | None => None
          | Some (error_description_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (group_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (instrument_optional_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (order_id_error_notice_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (auction_i_d_optional_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (original_message_type_value, bytes) =>
                                  match decode_bytes 200 bytes with
                                  | None => None
                                  | Some (error_detail_value, bytes) =>
                                      match decode_bytes 20 bytes with
                                      | None => None
                                      | Some (client_order_id_value, bytes) =>
                                          Some ({| error_code := error_code_value; error_description := error_description_value; group := group_value; instrument_optional := instrument_optional_value; order_id_error_notice := order_id_error_notice_value; auction_i_d_optional := auction_i_d_optional_value; original_message_type := original_message_type_value; error_detail := error_detail_value; client_order_id := client_order_id_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 358.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
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

  End ErrorNotice.

  Module BulkQuoteDataAcknowledgement.

    Record t := {
      group : list byte;
      trader_id : list byte;
      quote_i_d : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (quote_i_d record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (quote_i_d record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (quote_i_d_value, bytes) =>
                  Some ({| group := group_value; trader_id := trader_id_value; quote_i_d := quote_i_d_value |}, bytes)
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

  End BulkQuoteDataAcknowledgement.

  Module ClearingData.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData.

  Module OwnerData.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData.

  Module OrderAcknowledgement.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData.t;
      owner_data : OwnerData.t;
      original_order_id : list byte;
      reserved_6 : N;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData.bounded (clearing_data record) /\
      OwnerData.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      (reserved_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData.encode (clearing_data record) ++
      OwnerData.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_uint 6 (reserved_6 record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
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
                                      match ClearingData.decode bytes with
                                      | None => None
                                      | Some (clearing_data_value, bytes) =>
                                          match OwnerData.decode bytes with
                                          | None => None
                                          | Some (owner_data_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (original_order_id_value, bytes) =>
                                                  match decode_uint 6 bytes with
                                                  | None => None
                                                  | Some (reserved_6_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (additional_client_memo_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (reserved_4_value, bytes) =>
                                                              Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; reserved_6 := reserved_6_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 167.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData.encode_length, !OwnerData.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData.decode_encode by exact bound_8.
      rewrite OwnerData.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData.eq_dec | apply OwnerData.eq_dec]. Defined.

  End OrderAcknowledgement.

  Module GlobalCancellationConfirmation.

    Record t := {
      group : list byte;
      trader_id : list byte;
      type_of_cancellation : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (type_of_cancellation record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 1 (type_of_cancellation record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (type_of_cancellation_value, bytes) =>
                  Some ({| group := group_value; trader_id := trader_id_value; type_of_cancellation := type_of_cancellation_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End GlobalCancellationConfirmation.

  Module ClearingData2.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData2.

  Module OwnerData2.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData2.

  Module ImprovementOrderAcknowlegment.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData2.t;
      owner_data : OwnerData2.t;
      original_order_id : list byte;
      auction_i_d : list byte;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData2.bounded (clearing_data record) /\
      OwnerData2.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      Datatypes.length (auction_i_d record) = 6 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData2.encode (clearing_data record) ++
      OwnerData2.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_bytes 6 (auction_i_d record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
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
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (auction_i_d_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (additional_client_memo_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (reserved_4_value, bytes) =>
                                                              Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; auction_i_d := auction_i_d_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 167.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData2.encode_length, !OwnerData2.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData2.decode_encode by exact bound_8.
      rewrite OwnerData2.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData2.eq_dec | apply OwnerData2.eq_dec]. Defined.

  End ImprovementOrderAcknowlegment.

  Module ClearingData3.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData3.

  Module OwnerData3.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData3.

  Module OrderModificationAcknowledgement.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData3.t;
      owner_data : OwnerData3.t;
      original_order_id : list byte;
      reserved_6 : N;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData3.bounded (clearing_data record) /\
      OwnerData3.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      (reserved_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData3.encode (clearing_data record) ++
      OwnerData3.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_uint 6 (reserved_6 record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
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
                                                  | Some (reserved_6_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (additional_client_memo_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (reserved_4_value, bytes) =>
                                                              Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; reserved_6 := reserved_6_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 167.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData3.encode_length, !OwnerData3.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData3.decode_encode by exact bound_8.
      rewrite OwnerData3.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData3.eq_dec | apply OwnerData3.eq_dec]. Defined.

  End OrderModificationAcknowledgement.

  Module StandardAcknowledgement.

    Record t := {
      trader_id : list byte;
      original_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (original_message_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trader_id record) ++
      encode_bytes 2 (original_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (original_message_type_value, bytes) =>
              Some ({| trader_id := trader_id_value; original_message_type := original_message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End StandardAcknowledgement.

  Module ClearingData4.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData4.

  Module OwnerData4.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData4.

  Module ComplexOrderAuctionAcknowledgement.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData4.t;
      owner_data : OwnerData4.t;
      original_order_id : list byte;
      auction_i_d_optional : list byte;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData4.bounded (clearing_data record) /\
      OwnerData4.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData4.encode (clearing_data record) ++
      OwnerData4.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
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
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (auction_i_d_optional_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (additional_client_memo_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (reserved_4_value, bytes) =>
                                                              Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; auction_i_d_optional := auction_i_d_optional_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 167.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData4.encode_length, !OwnerData4.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData4.decode_encode by exact bound_8.
      rewrite OwnerData4.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData4.eq_dec | apply OwnerData4.eq_dec]. Defined.

  End ComplexOrderAuctionAcknowledgement.

  Module ClearingData5.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData5.

  Module OwnerData5.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData5.

  Module AuctionOrImprovementCancellationAcknowledgement.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData5.t;
      owner_data : OwnerData5.t;
      original_order_id : list byte;
      auction_i_d : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData5.bounded (clearing_data record) /\
      OwnerData5.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      Datatypes.length (auction_i_d record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData5.encode (clearing_data record) ++
      OwnerData5.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_bytes 6 (auction_i_d record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
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
                                      match ClearingData5.decode bytes with
                                      | None => None
                                      | Some (clearing_data_value, bytes) =>
                                          match OwnerData5.decode bytes with
                                          | None => None
                                          | Some (owner_data_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (original_order_id_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (auction_i_d_value, bytes) =>
                                                      Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; auction_i_d := auction_i_d_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 147.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData5.encode_length, !OwnerData5.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData5.decode_encode by exact bound_8.
      rewrite OwnerData5.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData5.eq_dec | apply OwnerData5.eq_dec]. Defined.

  End AuctionOrImprovementCancellationAcknowledgement.

  Module ClearingData6.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData6.

  Module OwnerData6.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData6.

  Module OrderCancellationAcknowledgement.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData6.t;
      owner_data : OwnerData6.t;
      original_order_id : list byte;
      auction_i_d : list byte;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData6.bounded (clearing_data record) /\
      OwnerData6.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      Datatypes.length (auction_i_d record) = 6 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData6.encode (clearing_data record) ++
      OwnerData6.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_bytes 6 (auction_i_d record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
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
                                      match ClearingData6.decode bytes with
                                      | None => None
                                      | Some (clearing_data_value, bytes) =>
                                          match OwnerData6.decode bytes with
                                          | None => None
                                          | Some (owner_data_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (original_order_id_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (auction_i_d_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (additional_client_memo_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (reserved_4_value, bytes) =>
                                                              Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; auction_i_d := auction_i_d_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 167.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData6.encode_length, !OwnerData6.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData6.decode_encode by exact bound_8.
      rewrite OwnerData6.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData6.eq_dec | apply OwnerData6.eq_dec]. Defined.

  End OrderCancellationAcknowledgement.

  Module TraderStatus.

    Record t := {
      trader_id : list byte;
      trader_lock_out : list byte;
      risk_team_lock_out : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (trader_lock_out record) = 1 /\
      Datatypes.length (risk_team_lock_out record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (trader_id record) ++
      encode_bytes 1 (trader_lock_out record) ++
      encode_bytes 1 (risk_team_lock_out record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trader_lock_out_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (risk_team_lock_out_value, bytes) =>
                  Some ({| trader_id := trader_id_value; trader_lock_out := trader_lock_out_value; risk_team_lock_out := risk_team_lock_out_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End TraderStatus.

  Module DirectedOrderCancellationNotice.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      verb_side : list byte;
      quantity : list byte;
      price : list byte;
      referenced_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (referenced_order_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 8 (referenced_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (verb_side_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (referenced_order_id_value, bytes) =>
                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; verb_side := verb_side_value; quantity := quantity_value; price := price_value; referenced_order_id := referenced_order_id_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DirectedOrderCancellationNotice.

  Module DirectedOrderNotice.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      verb_side : list byte;
      quantity : list byte;
      price : list byte;
      referenced_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (referenced_order_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 8 (referenced_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (verb_side_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (referenced_order_id_value, bytes) =>
                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; verb_side := verb_side_value; quantity := quantity_value; price := price_value; referenced_order_id := referenced_order_id_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DirectedOrderNotice.

  Module ExcludedInstrumentNotice.

    Record t := {
      group : list byte;
      reserved_2 : N;
      trader_id : list byte;
      second_reserved_2 : N;
      nb_of_instruments : list byte;
      instrument : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trader_id record) = 8 /\
      (second_reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (nb_of_instruments record) = 4 /\
      Datatypes.length (instrument record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_bytes 8 (trader_id record) ++
      encode_uint 2 (second_reserved_2 record) ++
      encode_bytes 4 (nb_of_instruments record) ++
      encode_bytes 4 (instrument record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (reserved_2_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (second_reserved_2_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (nb_of_instruments_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (instrument_value, bytes) =>
                              Some ({| group := group_value; reserved_2 := reserved_2_value; trader_id := trader_id_value; second_reserved_2 := second_reserved_2_value; nb_of_instruments := nb_of_instruments_value; instrument := instrument_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExcludedInstrumentNotice.

  Module GroupStateChange.

    Record t := {
      group : list byte;
      group_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (group_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 1 (group_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (group_state_value, bytes) =>
              Some ({| group := group_value; group_state := group_state_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End GroupStateChange.

  Module ClearingData7.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData7.

  Module OwnerData7.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData7.

  Module LegExecutionNotice.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      reference_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      time_trade_hhmmss : list byte;
      clearing_data : ClearingData7.t;
      owner_data : OwnerData7.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      auction_i_d_optional : list byte;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
      liquidity_status : list byte;
      strategy_group : list byte;
      strategy_instrument_id : list byte;
      strategy_verb_side : list byte;
      strategy_trade_number : list byte;
      leg_number : list byte;
      counterpart_account_type : list byte;
      additional_client_memo : list byte;
      reserved_1 : N;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (time_trade_hhmmss record) = 6 /\
      ClearingData7.bounded (clearing_data record) /\
      OwnerData7.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (strategy_group record) = 2 /\
      Datatypes.length (strategy_instrument_id record) = 4 /\
      Datatypes.length (strategy_verb_side record) = 1 /\
      Datatypes.length (strategy_trade_number record) = 8 /\
      Datatypes.length (leg_number record) = 2 /\
      Datatypes.length (counterpart_account_type record) = 1 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (time_trade_hhmmss record) ++
      ClearingData7.encode (clearing_data record) ++
      OwnerData7.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 2 (strategy_group record) ++
      encode_bytes 4 (strategy_instrument_id record) ++
      encode_bytes 1 (strategy_verb_side record) ++
      encode_bytes 8 (strategy_trade_number record) ++
      encode_bytes 2 (leg_number record) ++
      encode_bytes 1 (counterpart_account_type record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (reference_id_value, bytes) =>
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
                                  | Some (time_trade_hhmmss_value, bytes) =>
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
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (auction_i_d_optional_value, bytes) =>
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
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
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
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (counterpart_account_type_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (additional_client_memo_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (reserved_1_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (reserved_4_value, bytes) =>
                                                                                                                      Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; reference_id := reference_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; time_trade_hhmmss := time_trade_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; auction_i_d_optional := auction_i_d_optional_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value; liquidity_status := liquidity_status_value; strategy_group := strategy_group_value; strategy_instrument_id := strategy_instrument_id_value; strategy_verb_side := strategy_verb_side_value; strategy_trade_number := strategy_trade_number_value; leg_number := leg_number_value; counterpart_account_type := counterpart_account_type_value; additional_client_memo := additional_client_memo_value; reserved_1 := reserved_1_value; reserved_4 := reserved_4_value |}, bytes)
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 257.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData7.encode_length, !OwnerData7.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData7.decode_encode by exact bound_8.
      rewrite OwnerData7.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData7.eq_dec | apply OwnerData7.eq_dec]. Defined.

  End LegExecutionNotice.

  Module CancellationOfAllQuotesNotices.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      quote_cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (quote_cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 1 (quote_cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quote_cancel_reason_value, bytes) =>
                      Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; quote_cancel_reason := quote_cancel_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End CancellationOfAllQuotesNotices.

  Module QualityMarketMakerNotification.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      auction_i_d_optional : list byte;
      verb : list byte;
      auction_quantity : list byte;
      auction_price : list byte;
      quote_quantity : list byte;
      quote_price : list byte;
      qualified_quantity : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (verb record) = 1 /\
      Datatypes.length (auction_quantity record) = 8 /\
      Datatypes.length (auction_price record) = 10 /\
      Datatypes.length (quote_quantity record) = 8 /\
      Datatypes.length (quote_price record) = 10 /\
      Datatypes.length (qualified_quantity record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 1 (verb record) ++
      encode_bytes 8 (auction_quantity record) ++
      encode_bytes 10 (auction_price record) ++
      encode_bytes 8 (quote_quantity record) ++
      encode_bytes 10 (quote_price record) ++
      encode_bytes 8 (qualified_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (auction_i_d_optional_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (verb_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (auction_quantity_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (auction_price_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (quote_quantity_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (quote_price_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (qualified_quantity_value, bytes) =>
                                              Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; auction_i_d_optional := auction_i_d_optional_value; verb := verb_value; auction_quantity := auction_quantity_value; auction_price := auction_price_value; quote_quantity := quote_quantity_value; quote_price := quote_price_value; qualified_quantity := qualified_quantity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QualityMarketMakerNotification.

  Module ClearingData8.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData8.

  Module OwnerData8.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData8.

  Module ExecutionNotice.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      reference_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      time_of_the_trade_hhmmss : list byte;
      clearing_data : ClearingData8.t;
      owner_data : OwnerData8.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      auction_i_d_optional : list byte;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
      liquidity_status : list byte;
      counterpart_account_type : list byte;
      additional_client_memo : list byte;
      reserved_1 : N;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (time_of_the_trade_hhmmss record) = 6 /\
      ClearingData8.bounded (clearing_data record) /\
      OwnerData8.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (counterpart_account_type record) = 1 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (time_of_the_trade_hhmmss record) ++
      ClearingData8.encode (clearing_data record) ++
      OwnerData8.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (counterpart_account_type record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (reference_id_value, bytes) =>
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
                                  | Some (time_of_the_trade_hhmmss_value, bytes) =>
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
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (auction_i_d_optional_value, bytes) =>
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
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (counterpart_account_type_value, bytes) =>
                                                                                      match decode_bytes 16 bytes with
                                                                                      | None => None
                                                                                      | Some (additional_client_memo_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (reserved_1_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (reserved_4_value, bytes) =>
                                                                                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; reference_id := reference_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; time_of_the_trade_hhmmss := time_of_the_trade_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; auction_i_d_optional := auction_i_d_optional_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value; liquidity_status := liquidity_status_value; counterpart_account_type := counterpart_account_type_value; additional_client_memo := additional_client_memo_value; reserved_1 := reserved_1_value; reserved_4 := reserved_4_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 240.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData8.encode_length, !OwnerData8.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData8.decode_encode by exact bound_8.
      rewrite OwnerData8.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData8.eq_dec | apply OwnerData8.eq_dec]. Defined.

  End ExecutionNotice.

  Module QuoteNotice.

    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      reference_id_quote : list byte;
      verb_side : list byte;
      order_type : list byte;
      action : list byte;
      new_quantity : list byte;
      new_price : list byte;
      previous_quantity : list byte;
      previous_price : list byte;
      auction_i_d_optional : list byte;
      original_reference_id_quote_or_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id_quote record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (action record) = 1 /\
      Datatypes.length (new_quantity record) = 8 /\
      Datatypes.length (new_price record) = 10 /\
      Datatypes.length (previous_quantity record) = 8 /\
      Datatypes.length (previous_price record) = 10 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (original_reference_id_quote_or_order_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id_quote record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 1 (action record) ++
      encode_bytes 8 (new_quantity record) ++
      encode_bytes 10 (new_price record) ++
      encode_bytes 8 (previous_quantity record) ++
      encode_bytes 10 (previous_price record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 8 (original_reference_id_quote_or_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (reference_id_quote_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (verb_side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (order_type_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (action_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (new_quantity_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (new_price_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (previous_quantity_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (previous_price_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (auction_i_d_optional_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (original_reference_id_quote_or_order_id_value, bytes) =>
                                                          Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; reference_id_quote := reference_id_quote_value; verb_side := verb_side_value; order_type := order_type_value; action := action_value; new_quantity := new_quantity_value; new_price := new_price_value; previous_quantity := previous_quantity_value; previous_price := previous_price_value; auction_i_d_optional := auction_i_d_optional_value; original_reference_id_quote_or_order_id := original_reference_id_quote_or_order_id_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteNotice.

  Module ClearingData9.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData9.

  Module OwnerData9.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData9.

  Module ExecutionCancellationNotice.

    (** Stated by the guide as having the same number of bytes and format as NT, whose fields are written out here. *)
    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      reference_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      time_of_the_trade_hhmmss : list byte;
      clearing_data : ClearingData9.t;
      owner_data : OwnerData9.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      auction_i_d_optional : list byte;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
      liquidity_status : list byte;
      counterpart_account_type : list byte;
      additional_client_memo : list byte;
      reserved_1 : N;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (time_of_the_trade_hhmmss record) = 6 /\
      ClearingData9.bounded (clearing_data record) /\
      OwnerData9.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (counterpart_account_type record) = 1 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (time_of_the_trade_hhmmss record) ++
      ClearingData9.encode (clearing_data record) ++
      OwnerData9.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (counterpart_account_type record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (reference_id_value, bytes) =>
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
                                  | Some (time_of_the_trade_hhmmss_value, bytes) =>
                                      match ClearingData9.decode bytes with
                                      | None => None
                                      | Some (clearing_data_value, bytes) =>
                                          match OwnerData9.decode bytes with
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
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (auction_i_d_optional_value, bytes) =>
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
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (counterpart_account_type_value, bytes) =>
                                                                                      match decode_bytes 16 bytes with
                                                                                      | None => None
                                                                                      | Some (additional_client_memo_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (reserved_1_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (reserved_4_value, bytes) =>
                                                                                                  Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; reference_id := reference_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; time_of_the_trade_hhmmss := time_of_the_trade_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; auction_i_d_optional := auction_i_d_optional_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value; liquidity_status := liquidity_status_value; counterpart_account_type := counterpart_account_type_value; additional_client_memo := additional_client_memo_value; reserved_1 := reserved_1_value; reserved_4 := reserved_4_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 240.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData9.encode_length, !OwnerData9.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData9.decode_encode by exact bound_8.
      rewrite OwnerData9.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData9.eq_dec | apply OwnerData9.eq_dec]. Defined.

  End ExecutionCancellationNotice.

  Module ClearingData10.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData10.

  Module OwnerData10.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData10.

  Module LegExecutionCancellationNotice.

    (** Stated by the guide as having the same number of bytes and format as NL, whose fields are written out here. *)
    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      reference_id : list byte;
      verb_side : list byte;
      quantity_traded : list byte;
      trade_price : list byte;
      time_trade_hhmmss : list byte;
      clearing_data : ClearingData10.t;
      owner_data : OwnerData10.t;
      special_trade_indicator : list byte;
      price_type : list byte;
      trade_type : list byte;
      auction_i_d_optional : list byte;
      trade_number : list byte;
      trade_memo : list byte;
      original_reference_id : list byte;
      id_code_for_the_counterpart_participant : list byte;
      liquidity_status : list byte;
      strategy_group : list byte;
      strategy_instrument_id : list byte;
      strategy_verb_side : list byte;
      strategy_trade_number : list byte;
      leg_number : list byte;
      counterpart_account_type : list byte;
      additional_client_memo : list byte;
      reserved_1 : N;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (reference_id record) = 8 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_traded record) = 8 /\
      Datatypes.length (trade_price record) = 10 /\
      Datatypes.length (time_trade_hhmmss record) = 6 /\
      ClearingData10.bounded (clearing_data record) /\
      OwnerData10.bounded (owner_data record) /\
      Datatypes.length (special_trade_indicator record) = 1 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (auction_i_d_optional record) = 6 /\
      Datatypes.length (trade_number record) = 8 /\
      Datatypes.length (trade_memo record) = 50 /\
      Datatypes.length (original_reference_id record) = 8 /\
      Datatypes.length (id_code_for_the_counterpart_participant record) = 4 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (strategy_group record) = 2 /\
      Datatypes.length (strategy_instrument_id record) = 4 /\
      Datatypes.length (strategy_verb_side record) = 1 /\
      Datatypes.length (strategy_trade_number record) = 8 /\
      Datatypes.length (leg_number record) = 2 /\
      Datatypes.length (counterpart_account_type record) = 1 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (reference_id record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity_traded record) ++
      encode_bytes 10 (trade_price record) ++
      encode_bytes 6 (time_trade_hhmmss record) ++
      ClearingData10.encode (clearing_data record) ++
      OwnerData10.encode (owner_data record) ++
      encode_bytes 1 (special_trade_indicator record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 6 (auction_i_d_optional record) ++
      encode_bytes 8 (trade_number record) ++
      encode_bytes 50 (trade_memo record) ++
      encode_bytes 8 (original_reference_id record) ++
      encode_bytes 4 (id_code_for_the_counterpart_participant record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 2 (strategy_group record) ++
      encode_bytes 4 (strategy_instrument_id record) ++
      encode_bytes 1 (strategy_verb_side record) ++
      encode_bytes 8 (strategy_trade_number record) ++
      encode_bytes 2 (leg_number record) ++
      encode_bytes 1 (counterpart_account_type record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trader_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (reference_id_value, bytes) =>
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
                                  | Some (time_trade_hhmmss_value, bytes) =>
                                      match ClearingData10.decode bytes with
                                      | None => None
                                      | Some (clearing_data_value, bytes) =>
                                          match OwnerData10.decode bytes with
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
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (auction_i_d_optional_value, bytes) =>
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
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
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
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (counterpart_account_type_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (additional_client_memo_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (reserved_1_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (reserved_4_value, bytes) =>
                                                                                                                      Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; reference_id := reference_id_value; verb_side := verb_side_value; quantity_traded := quantity_traded_value; trade_price := trade_price_value; time_trade_hhmmss := time_trade_hhmmss_value; clearing_data := clearing_data_value; owner_data := owner_data_value; special_trade_indicator := special_trade_indicator_value; price_type := price_type_value; trade_type := trade_type_value; auction_i_d_optional := auction_i_d_optional_value; trade_number := trade_number_value; trade_memo := trade_memo_value; original_reference_id := original_reference_id_value; id_code_for_the_counterpart_participant := id_code_for_the_counterpart_participant_value; liquidity_status := liquidity_status_value; strategy_group := strategy_group_value; strategy_instrument_id := strategy_instrument_id_value; strategy_verb_side := strategy_verb_side_value; strategy_trade_number := strategy_trade_number_value; leg_number := leg_number_value; counterpart_account_type := counterpart_account_type_value; additional_client_memo := additional_client_memo_value; reserved_1 := reserved_1_value; reserved_4 := reserved_4_value |}, bytes)
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 257.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData10.encode_length, !OwnerData10.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData10.decode_encode by exact bound_8.
      rewrite OwnerData10.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData10.eq_dec | apply OwnerData10.eq_dec]. Defined.

  End LegExecutionCancellationNotice.

  Module ClearingData11.

    (** The guide states these fields once, as Clearing Data, for every message that carries them. *)
    Record t := {
      clearing_instruction : list byte;
      account_type : list byte;
      open_close : list byte;
      hedge_spec : list byte;
      clearing_operation_mode : list byte;
      clearing_destination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (clearing_instruction record) = 12 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (hedge_spec record) = 1 /\
      Datatypes.length (clearing_operation_mode record) = 1 /\
      Datatypes.length (clearing_destination record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (clearing_instruction record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 1 (hedge_spec record) ++
      encode_bytes 1 (clearing_operation_mode record) ++
      encode_bytes 4 (clearing_destination record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (clearing_operation_mode_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (clearing_destination_value, bytes) =>
                              Some ({| clearing_instruction := clearing_instruction_value; account_type := account_type_value; open_close := open_close_value; hedge_spec := hedge_spec_value; clearing_operation_mode := clearing_operation_mode_value; clearing_destination := clearing_destination_value |}, bytes)
                          end
                      end
                  end
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

  End ClearingData11.

  Module OwnerData11.

    (** The guide states these fields once, as Owner Data, for every message that carries them. *)
    Record t := {
      client_order_id : list byte;
      pound_sign : list byte;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (pound_sign record) = 1 /\
      Datatypes.length (memo record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (pound_sign record) ++
      encode_bytes 50 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (pound_sign_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (memo_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; pound_sign := pound_sign_value; memo := memo_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End OwnerData11.

  Module OrderCancellationNoticeBySystem.

    (** Stated by the guide as having the same number of bytes and format as KZ, whose fields are written out here. *)
    Record t := {
      group : list byte;
      instrument_optional : list byte;
      trader_id : list byte;
      order_id : list byte;
      status : list byte;
      verb_side : list byte;
      quantity : list byte;
      assigned_price : list byte;
      clearing_data : ClearingData11.t;
      owner_data : OwnerData11.t;
      original_order_id : list byte;
      auction_i_d : list byte;
      additional_client_memo : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument_optional record) = 4 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (order_id record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (assigned_price record) = 10 /\
      ClearingData11.bounded (clearing_data record) /\
      OwnerData11.bounded (owner_data record) /\
      Datatypes.length (original_order_id record) = 8 /\
      Datatypes.length (auction_i_d record) = 6 /\
      Datatypes.length (additional_client_memo record) = 16 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument_optional record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (assigned_price record) ++
      ClearingData11.encode (clearing_data record) ++
      OwnerData11.encode (owner_data record) ++
      encode_bytes 8 (original_order_id record) ++
      encode_bytes 6 (auction_i_d record) ++
      encode_bytes 16 (additional_client_memo record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (group_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (instrument_optional_value, bytes) =>
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
                                      match ClearingData11.decode bytes with
                                      | None => None
                                      | Some (clearing_data_value, bytes) =>
                                          match OwnerData11.decode bytes with
                                          | None => None
                                          | Some (owner_data_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (original_order_id_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (auction_i_d_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (additional_client_memo_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (reserved_4_value, bytes) =>
                                                              Some ({| group := group_value; instrument_optional := instrument_optional_value; trader_id := trader_id_value; order_id := order_id_value; status := status_value; verb_side := verb_side_value; quantity := quantity_value; assigned_price := assigned_price_value; clearing_data := clearing_data_value; owner_data := owner_data_value; original_order_id := original_order_id_value; auction_i_d := auction_i_d_value; additional_client_memo := additional_client_memo_value; reserved_4 := reserved_4_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 167.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ClearingData11.encode_length, !OwnerData11.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite ClearingData11.decode_encode by exact bound_8.
      rewrite OwnerData11.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClearingData11.eq_dec | apply OwnerData11.eq_dec]. Defined.

  End OrderCancellationNoticeBySystem.

End BoxOptionsSolaOrderEntryV225Exchange.
