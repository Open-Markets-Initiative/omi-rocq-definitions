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

Module MxSolaOrderEntryV121Firm.

  Module HeartbeatResponse.

    Record t := {
      user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period : list byte;
      last_exchange_message_id_sent_to_participant : list byte;
      user_message_timestamp_local_hhmmss : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period record) = 8 /\
      Datatypes.length (last_exchange_message_id_sent_to_participant record) = 6 /\
      Datatypes.length (user_message_timestamp_local_hhmmss record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period record) ++
      encode_bytes 6 (last_exchange_message_id_sent_to_participant record) ++
      encode_bytes 6 (user_message_timestamp_local_hhmmss record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (last_exchange_message_id_sent_to_participant_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (user_message_timestamp_local_hhmmss_value, bytes) =>
                  Some ({| user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period := user_sequence_id_first_user_sequence_id_for_nextcurrent_heartbeat_period_value; last_exchange_message_id_sent_to_participant := last_exchange_message_id_sent_to_participant_value; user_message_timestamp_local_hhmmss := user_message_timestamp_local_hhmmss_value |}, bytes)
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

  End HeartbeatResponse.

  Module UserDisconnection.

    Record t := {
      user_id : list byte;
      session_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 8 /\
      Datatypes.length (session_id record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (user_id record) ++
      encode_bytes 4 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              Some ({| user_id := user_id_value; session_id := session_id_value |}, bytes)
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

  End UserDisconnection.

  Module IncomingMessagesHeader.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader.

  Module OrderRequest.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader.bounded (incoming_messages_header record).

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader.encode (incoming_messages_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          Some ({| incoming_messages_header := incoming_messages_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !IncomingMessagesHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite IncomingMessagesHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply IncomingMessagesHeader.eq_dec]. Defined.

  End OrderRequest.

  Module IncomingMessagesHeader2.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader2.

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

  Module BulkQuoteData.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader2.t;
      group : list byte;
      clearing_data : ClearingData.t;
      owner_data : OwnerData.t;
      maximum_number_trades : list byte;
      minimum_volume : list byte;
      filler_2 : N;
      calculation_time_interval : list byte;
      maximum_total_volume : list byte;
      maximum_total_value : list byte;
      delta_maximum_volume : list byte;
      delta_maximum_value : list byte;
      anti_wash_id : list byte;
      filler_20 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader2.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      ClearingData.bounded (clearing_data record) /\
      OwnerData.bounded (owner_data record) /\
      Datatypes.length (maximum_number_trades record) = 2 /\
      Datatypes.length (minimum_volume record) = 8 /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (calculation_time_interval record) = 8 /\
      Datatypes.length (maximum_total_volume record) = 8 /\
      Datatypes.length (maximum_total_value record) = 8 /\
      Datatypes.length (delta_maximum_volume record) = 8 /\
      Datatypes.length (delta_maximum_value record) = 8 /\
      Datatypes.length (anti_wash_id record) = 8 /\
      Datatypes.length (filler_20 record) = 20.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader2.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      ClearingData.encode (clearing_data record) ++
      OwnerData.encode (owner_data record) ++
      encode_bytes 2 (maximum_number_trades record) ++
      encode_bytes 8 (minimum_volume record) ++
      encode_uint 2 (filler_2 record) ++
      encode_bytes 8 (calculation_time_interval record) ++
      encode_bytes 8 (maximum_total_volume record) ++
      encode_bytes 8 (maximum_total_value record) ++
      encode_bytes 8 (delta_maximum_volume record) ++
      encode_bytes 8 (delta_maximum_value record) ++
      encode_bytes 8 (anti_wash_id record) ++
      encode_bytes 20 (filler_20 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader2.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match ClearingData.decode bytes with
              | None => None
              | Some (clearing_data_value, bytes) =>
                  match OwnerData.decode bytes with
                  | None => None
                  | Some (owner_data_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (maximum_number_trades_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (minimum_volume_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (filler_2_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (calculation_time_interval_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (maximum_total_volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (maximum_total_value_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (delta_maximum_volume_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (delta_maximum_value_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (anti_wash_id_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (filler_20_value, bytes) =>
                                                              Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; clearing_data := clearing_data_value; owner_data := owner_data_value; maximum_number_trades := maximum_number_trades_value; minimum_volume := minimum_volume_value; filler_2 := filler_2_value; calculation_time_interval := calculation_time_interval_value; maximum_total_volume := maximum_total_volume_value; maximum_total_value := maximum_total_value_value; delta_maximum_volume := delta_maximum_volume_value; delta_maximum_value := delta_maximum_value_value; anti_wash_id := anti_wash_id_value; filler_20 := filler_20_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 174.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader2.encode_length, !encode_bytes_length, !ClearingData.encode_length, !OwnerData.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader2.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite ClearingData.decode_encode by exact bound_2.
      rewrite OwnerData.decode_encode by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader2.eq_dec | apply ClearingData.eq_dec | apply OwnerData.eq_dec]. Defined.

  End BulkQuoteData.

  Module IncomingMessagesHeader3.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader3.

  Module IncomingMessagesHeader4.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader4.

  Module GlobalCancellation.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader4.t;
      group : list byte;
      type_of_cancellation_q_quotes_only : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader4.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (type_of_cancellation_q_quotes_only record) = 1.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader4.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 1 (type_of_cancellation_q_quotes_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader4.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (type_of_cancellation_q_quotes_only_value, bytes) =>
                  Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; type_of_cancellation_q_quotes_only := type_of_cancellation_q_quotes_only_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader4.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader4.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader4.eq_dec]. Defined.

  End GlobalCancellation.

  Module IncomingMessagesHeader5.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader5.

  Module UserGlobalCancellation.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader5.t;
      group_filter : list byte;
      instrument_filter : list byte;
      type_of_cancellation : list byte;
      account_type_filter : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader5.bounded (incoming_messages_header record) /\
      Datatypes.length (group_filter record) = 2 /\
      Datatypes.length (instrument_filter record) = 4 /\
      Datatypes.length (type_of_cancellation record) = 1 /\
      Datatypes.length (account_type_filter record) = 8.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader5.encode (incoming_messages_header record) ++
      encode_bytes 2 (group_filter record) ++
      encode_bytes 4 (instrument_filter record) ++
      encode_bytes 1 (type_of_cancellation record) ++
      encode_bytes 8 (account_type_filter record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader5.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_filter_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_filter_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (type_of_cancellation_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (account_type_filter_value, bytes) =>
                          Some ({| incoming_messages_header := incoming_messages_header_value; group_filter := group_filter_value; instrument_filter := instrument_filter_value; type_of_cancellation := type_of_cancellation_value; account_type_filter := account_type_filter_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader5.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader5.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader5.eq_dec]. Defined.

  End UserGlobalCancellation.

  Module IncomingMessagesHeader6.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader6.

  Module IncomingMessagesHeader7.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader7.

  Module SetGlobalRiskLimits.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader7.t;
      global_net_exposure_action : list byte;
      default_net_exposure_action : list byte;
      default_long_exposure_action : list byte;
      default_short_exposure_action : list byte;
      default_net_position_action : list byte;
      default_long_position_action : list byte;
      default_short_position_action : list byte;
      global_net_exposure_limit : list byte;
      default_maximum_order_quantity : list byte;
      default_net_exposure_limit : list byte;
      default_long_exposure_limit : list byte;
      default_short_exposure_limit : list byte;
      default_net_position_limit : list byte;
      default_long_position_limit : list byte;
      default_short_position_limit : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader7.bounded (incoming_messages_header record) /\
      Datatypes.length (global_net_exposure_action record) = 1 /\
      Datatypes.length (default_net_exposure_action record) = 1 /\
      Datatypes.length (default_long_exposure_action record) = 1 /\
      Datatypes.length (default_short_exposure_action record) = 1 /\
      Datatypes.length (default_net_position_action record) = 1 /\
      Datatypes.length (default_long_position_action record) = 1 /\
      Datatypes.length (default_short_position_action record) = 1 /\
      Datatypes.length (global_net_exposure_limit record) = 10 /\
      Datatypes.length (default_maximum_order_quantity record) = 8 /\
      Datatypes.length (default_net_exposure_limit record) = 10 /\
      Datatypes.length (default_long_exposure_limit record) = 10 /\
      Datatypes.length (default_short_exposure_limit record) = 10 /\
      Datatypes.length (default_net_position_limit record) = 8 /\
      Datatypes.length (default_long_position_limit record) = 8 /\
      Datatypes.length (default_short_position_limit record) = 8.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader7.encode (incoming_messages_header record) ++
      encode_bytes 1 (global_net_exposure_action record) ++
      encode_bytes 1 (default_net_exposure_action record) ++
      encode_bytes 1 (default_long_exposure_action record) ++
      encode_bytes 1 (default_short_exposure_action record) ++
      encode_bytes 1 (default_net_position_action record) ++
      encode_bytes 1 (default_long_position_action record) ++
      encode_bytes 1 (default_short_position_action record) ++
      encode_bytes 10 (global_net_exposure_limit record) ++
      encode_bytes 8 (default_maximum_order_quantity record) ++
      encode_bytes 10 (default_net_exposure_limit record) ++
      encode_bytes 10 (default_long_exposure_limit record) ++
      encode_bytes 10 (default_short_exposure_limit record) ++
      encode_bytes 8 (default_net_position_limit record) ++
      encode_bytes 8 (default_long_position_limit record) ++
      encode_bytes 8 (default_short_position_limit record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader7.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (global_net_exposure_action_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (default_net_exposure_action_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (default_long_exposure_action_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (default_short_exposure_action_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (default_net_position_action_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (default_long_position_action_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (default_short_position_action_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (global_net_exposure_limit_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (default_maximum_order_quantity_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (default_net_exposure_limit_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (default_long_exposure_limit_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (default_short_exposure_limit_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (default_net_position_limit_value, bytes) =>
                                                              match decode_bytes 8 bytes with
                                                              | None => None
                                                              | Some (default_long_position_limit_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (default_short_position_limit_value, bytes) =>
                                                                      Some ({| incoming_messages_header := incoming_messages_header_value; global_net_exposure_action := global_net_exposure_action_value; default_net_exposure_action := default_net_exposure_action_value; default_long_exposure_action := default_long_exposure_action_value; default_short_exposure_action := default_short_exposure_action_value; default_net_position_action := default_net_position_action_value; default_long_position_action := default_long_position_action_value; default_short_position_action := default_short_position_action_value; global_net_exposure_limit := global_net_exposure_limit_value; default_maximum_order_quantity := default_maximum_order_quantity_value; default_net_exposure_limit := default_net_exposure_limit_value; default_long_exposure_limit := default_long_exposure_limit_value; default_short_exposure_limit := default_short_exposure_limit_value; default_net_position_limit := default_net_position_limit_value; default_long_position_limit := default_long_position_limit_value; default_short_position_limit := default_short_position_limit_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader7.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader7.decode_encode by exact bound_0.
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader7.eq_dec]. Defined.

  End SetGlobalRiskLimits.

  Module IncomingMessagesHeader8.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader8.

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

  Module OrderEntry.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader8.t;
      group : list byte;
      instrument : list byte;
      price_type : list byte;
      verb_side : list byte;
      quantity : list byte;
      price : list byte;
      special_price_term : list byte;
      additional_price : list byte;
      quantity_term : list byte;
      additional_quantity : list byte;
      duration_type : list byte;
      gtd_date : list byte;
      executing_participant : list byte;
      filler_1 : N;
      clearing_data : ClearingData2.t;
      owner_data : OwnerData2.t;
      anti_wash_id : list byte;
      anti_wash_instruction : list byte;
      filler_20 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader8.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (special_price_term record) = 1 /\
      Datatypes.length (additional_price record) = 10 /\
      Datatypes.length (quantity_term record) = 1 /\
      Datatypes.length (additional_quantity record) = 8 /\
      Datatypes.length (duration_type record) = 1 /\
      Datatypes.length (gtd_date record) = 8 /\
      Datatypes.length (executing_participant record) = 4 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      ClearingData2.bounded (clearing_data record) /\
      OwnerData2.bounded (owner_data record) /\
      Datatypes.length (anti_wash_id record) = 8 /\
      Datatypes.length (anti_wash_instruction record) = 1 /\
      Datatypes.length (filler_20 record) = 20.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader8.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 1 (special_price_term record) ++
      encode_bytes 10 (additional_price record) ++
      encode_bytes 1 (quantity_term record) ++
      encode_bytes 8 (additional_quantity record) ++
      encode_bytes 1 (duration_type record) ++
      encode_bytes 8 (gtd_date record) ++
      encode_bytes 4 (executing_participant record) ++
      encode_uint 1 (filler_1 record) ++
      ClearingData2.encode (clearing_data record) ++
      OwnerData2.encode (owner_data record) ++
      encode_bytes 8 (anti_wash_id record) ++
      encode_bytes 1 (anti_wash_instruction record) ++
      encode_bytes 20 (filler_20 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader8.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (price_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (verb_side_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (special_price_term_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (additional_price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (quantity_term_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (additional_quantity_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (duration_type_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (gtd_date_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (executing_participant_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (filler_1_value, bytes) =>
                                                                  match ClearingData2.decode bytes with
                                                                  | None => None
                                                                  | Some (clearing_data_value, bytes) =>
                                                                      match OwnerData2.decode bytes with
                                                                      | None => None
                                                                      | Some (owner_data_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (anti_wash_id_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (anti_wash_instruction_value, bytes) =>
                                                                                  match decode_bytes 20 bytes with
                                                                                  | None => None
                                                                                  | Some (filler_20_value, bytes) =>
                                                                                      Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; instrument := instrument_value; price_type := price_type_value; verb_side := verb_side_value; quantity := quantity_value; price := price_value; special_price_term := special_price_term_value; additional_price := additional_price_value; quantity_term := quantity_term_value; additional_quantity := additional_quantity_value; duration_type := duration_type_value; gtd_date := gtd_date_value; executing_participant := executing_participant_value; filler_1 := filler_1_value; clearing_data := clearing_data_value; owner_data := owner_data_value; anti_wash_id := anti_wash_id_value; anti_wash_instruction := anti_wash_instruction_value; filler_20 := filler_20_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 181.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader8.encode_length, !encode_bytes_length, !encode_uint_length, !ClearingData2.encode_length, !OwnerData2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader8.decode_encode by exact bound_0.
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite ClearingData2.decode_encode by exact bound_15.
      rewrite OwnerData2.decode_encode by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader8.eq_dec | apply ClearingData2.eq_dec | apply OwnerData2.eq_dec]. Defined.

  End OrderEntry.

  Module IncomingMessagesHeader9.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader9.

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

  Module OrderModification.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader9.t;
      group : list byte;
      instrument : list byte;
      price_type : list byte;
      verb_side : list byte;
      quantity_sign : list byte;
      quantity : list byte;
      price : list byte;
      special_price_term : list byte;
      additional_price : list byte;
      quantity_term : list byte;
      additional_quantity : list byte;
      duration_type : list byte;
      gtd_date : list byte;
      filler_4 : N;
      filler_1 : N;
      modified_order_id : list byte;
      clearing_data : ClearingData3.t;
      owner_data : OwnerData3.t;
      anti_wash_id : list byte;
      anti_wash_instruction : list byte;
      filler_20 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader9.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (verb_side record) = 1 /\
      Datatypes.length (quantity_sign record) = 1 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (special_price_term record) = 1 /\
      Datatypes.length (additional_price record) = 10 /\
      Datatypes.length (quantity_term record) = 1 /\
      Datatypes.length (additional_quantity record) = 8 /\
      Datatypes.length (duration_type record) = 1 /\
      Datatypes.length (gtd_date record) = 8 /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (modified_order_id record) = 8 /\
      ClearingData3.bounded (clearing_data record) /\
      OwnerData3.bounded (owner_data record) /\
      Datatypes.length (anti_wash_id record) = 8 /\
      Datatypes.length (anti_wash_instruction record) = 1 /\
      Datatypes.length (filler_20 record) = 20.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader9.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 1 (verb_side record) ++
      encode_bytes 1 (quantity_sign record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 1 (special_price_term record) ++
      encode_bytes 10 (additional_price record) ++
      encode_bytes 1 (quantity_term record) ++
      encode_bytes 8 (additional_quantity record) ++
      encode_bytes 1 (duration_type record) ++
      encode_bytes 8 (gtd_date record) ++
      encode_uint 4 (filler_4 record) ++
      encode_uint 1 (filler_1 record) ++
      encode_bytes 8 (modified_order_id record) ++
      ClearingData3.encode (clearing_data record) ++
      OwnerData3.encode (owner_data record) ++
      encode_bytes 8 (anti_wash_id record) ++
      encode_bytes 1 (anti_wash_instruction record) ++
      encode_bytes 20 (filler_20 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader9.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (price_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (verb_side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (quantity_sign_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (special_price_term_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (additional_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quantity_term_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (additional_quantity_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (duration_type_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (gtd_date_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (filler_4_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (filler_1_value, bytes) =>
                                                                      match decode_bytes 8 bytes with
                                                                      | None => None
                                                                      | Some (modified_order_id_value, bytes) =>
                                                                          match ClearingData3.decode bytes with
                                                                          | None => None
                                                                          | Some (clearing_data_value, bytes) =>
                                                                              match OwnerData3.decode bytes with
                                                                              | None => None
                                                                              | Some (owner_data_value, bytes) =>
                                                                                  match decode_bytes 8 bytes with
                                                                                  | None => None
                                                                                  | Some (anti_wash_id_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (anti_wash_instruction_value, bytes) =>
                                                                                          match decode_bytes 20 bytes with
                                                                                          | None => None
                                                                                          | Some (filler_20_value, bytes) =>
                                                                                              Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; instrument := instrument_value; price_type := price_type_value; verb_side := verb_side_value; quantity_sign := quantity_sign_value; quantity := quantity_value; price := price_value; special_price_term := special_price_term_value; additional_price := additional_price_value; quantity_term := quantity_term_value; additional_quantity := additional_quantity_value; duration_type := duration_type_value; gtd_date := gtd_date_value; filler_4 := filler_4_value; filler_1 := filler_1_value; modified_order_id := modified_order_id_value; clearing_data := clearing_data_value; owner_data := owner_data_value; anti_wash_id := anti_wash_id_value; anti_wash_instruction := anti_wash_instruction_value; filler_20 := filler_20_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 190.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader9.encode_length, !encode_bytes_length, !encode_uint_length, !ClearingData3.encode_length, !OwnerData3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader9.decode_encode by exact bound_0.
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite ClearingData3.decode_encode by exact bound_17.
      rewrite OwnerData3.decode_encode by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader9.eq_dec | apply ClearingData3.eq_dec | apply OwnerData3.eq_dec]. Defined.

  End OrderModification.

  Module IncomingMessagesHeader10.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader10.

  Module IncomingMessagesHeader11.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader11.

  Module BuyingClearingData.

    (** Clearing Data for the buying side, which OX: Cross Entry carries alongside the other side. *)
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

  End BuyingClearingData.

  Module SellingClearingData.

    (** Clearing Data for the selling side, which OX: Cross Entry carries alongside the other side. *)
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

  End SellingClearingData.

  Module BuyingOwnerData.

    (** Owner Data for the buying side, which OX: Cross Entry carries alongside the other side. *)
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

  End BuyingOwnerData.

  Module SellingOwnerData.

    (** Owner Data for the selling side, which OX: Cross Entry carries alongside the other side. *)
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

  End SellingOwnerData.

  Module CrossEntry.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader11.t;
      group : list byte;
      instrument : list byte;
      filler_1 : N;
      quantity : list byte;
      price : list byte;
      buying_clearing_data : BuyingClearingData.t;
      selling_clearing_data : SellingClearingData.t;
      buying_owner_data : BuyingOwnerData.t;
      selling_owner_data : SellingOwnerData.t;
      filler_20 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader11.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (price record) = 10 /\
      BuyingClearingData.bounded (buying_clearing_data record) /\
      SellingClearingData.bounded (selling_clearing_data record) /\
      BuyingOwnerData.bounded (buying_owner_data record) /\
      SellingOwnerData.bounded (selling_owner_data record) /\
      Datatypes.length (filler_20 record) = 20.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader11.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_uint 1 (filler_1 record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 10 (price record) ++
      BuyingClearingData.encode (buying_clearing_data record) ++
      SellingClearingData.encode (selling_clearing_data record) ++
      BuyingOwnerData.encode (buying_owner_data record) ++
      SellingOwnerData.encode (selling_owner_data record) ++
      encode_bytes 20 (filler_20 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader11.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (filler_1_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match BuyingClearingData.decode bytes with
                              | None => None
                              | Some (buying_clearing_data_value, bytes) =>
                                  match SellingClearingData.decode bytes with
                                  | None => None
                                  | Some (selling_clearing_data_value, bytes) =>
                                      match BuyingOwnerData.decode bytes with
                                      | None => None
                                      | Some (buying_owner_data_value, bytes) =>
                                          match SellingOwnerData.decode bytes with
                                          | None => None
                                          | Some (selling_owner_data_value, bytes) =>
                                              match decode_bytes 20 bytes with
                                              | None => None
                                              | Some (filler_20_value, bytes) =>
                                                  Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; instrument := instrument_value; filler_1 := filler_1_value; quantity := quantity_value; price := price_value; buying_clearing_data := buying_clearing_data_value; selling_clearing_data := selling_clearing_data_value; buying_owner_data := buying_owner_data_value; selling_owner_data := selling_owner_data_value; filler_20 := filler_20_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 207.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader11.encode_length, !encode_bytes_length, !encode_uint_length, !BuyingClearingData.encode_length, !SellingClearingData.encode_length, !BuyingOwnerData.encode_length, !SellingOwnerData.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader11.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite BuyingClearingData.decode_encode by exact bound_6.
      rewrite SellingClearingData.decode_encode by exact bound_7.
      rewrite BuyingOwnerData.decode_encode by exact bound_8.
      rewrite SellingOwnerData.decode_encode by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader11.eq_dec | apply BuyingClearingData.eq_dec | apply SellingClearingData.eq_dec | apply BuyingOwnerData.eq_dec | apply SellingOwnerData.eq_dec]. Defined.

  End CrossEntry.

  Module IncomingMessagesHeader12.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader12.

  Module IncomingMessagesHeader13.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader13.

  Module IncomingMessagesHeader14.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader14.

  Module IncomingMessagesHeader15.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader15.

  Module IncomingMessagesHeader16.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader16.

  Module IncomingMessagesHeader17.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader17.

  Module IncomingMessagesHeader18.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader18.

  Module IncomingMessagesHeader19.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader19.

  Module IncomingMessagesHeader20.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader20.

  Module IncomingMessagesHeader21.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader21.

  Module IncomingMessagesHeader22.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader22.

  Module IncomingMessagesHeader23.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader23.

  Module IncomingMessagesHeader24.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader24.

  Module IncomingMessagesHeader25.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader25.

  Module IncomingMessagesHeader26.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader26.

  Module IncomingMessagesHeader27.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader27.

  Module IncomingMessagesHeader28.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader28.

  Module SailRequestForQuoteWithSide.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader28.t;
      group : list byte;
      instrument : list byte;
      quantity : list byte;
      market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader28.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (quantity record) = 8 /\
      Datatypes.length (market_side record) = 1.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader28.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (quantity record) ++
      encode_bytes 1 (market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader28.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
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
                          Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; instrument := instrument_value; quantity := quantity_value; market_side := market_side_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader28.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader28.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader28.eq_dec]. Defined.

  End SailRequestForQuoteWithSide.

  Module IncomingMessagesHeader29.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader29.

  Module BulkQuoteParticipantBqpProtectionSubscription.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader29.t;
      group : list byte;
      protection_type_advanced_protection_advanced_protection_disabled : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader29.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (protection_type_advanced_protection_advanced_protection_disabled record) = 1.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader29.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 1 (protection_type_advanced_protection_advanced_protection_disabled record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader29.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (protection_type_advanced_protection_advanced_protection_disabled_value, bytes) =>
                  Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; protection_type_advanced_protection_advanced_protection_disabled := protection_type_advanced_protection_advanced_protection_disabled_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader29.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader29.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader29.eq_dec]. Defined.

  End BulkQuoteParticipantBqpProtectionSubscription.

  Module IncomingMessagesHeader30.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader30.

  Module RequestForQuote.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader30.t;
      group : list byte;
      instrument : list byte;
      quantity : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader30.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (quantity record) = 8.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader30.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader30.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; instrument := instrument_value; quantity := quantity_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader30.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader30.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader30.eq_dec]. Defined.

  End RequestForQuote.

  Module IncomingMessagesHeader31.

    (** The guide states these fields once, as the Incoming Messages Header, for every business message a Participant sends. Message Type is read by the packet before the branch, so it is not repeated here. *)
    Record t := {
      user_timestamp_local_hhmmss : list byte;
      trader_id : list byte;
      user_sequence_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_timestamp_local_hhmmss record) = 6 /\
      Datatypes.length (trader_id record) = 8 /\
      Datatypes.length (user_sequence_id record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_timestamp_local_hhmmss record) ++
      encode_bytes 8 (trader_id record) ++
      encode_bytes 8 (user_sequence_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_timestamp_local_hhmmss_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (user_sequence_id_value, bytes) =>
                  Some ({| user_timestamp_local_hhmmss := user_timestamp_local_hhmmss_value; trader_id := trader_id_value; user_sequence_id := user_sequence_id_value |}, bytes)
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

  End IncomingMessagesHeader31.

  Module OrderCancellation.

    Record t := {
      incoming_messages_header : IncomingMessagesHeader31.t;
      group : list byte;
      instrument : list byte;
      cancelled_order_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      IncomingMessagesHeader31.bounded (incoming_messages_header record) /\
      Datatypes.length (group record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (cancelled_order_id record) = 8.

    Definition encode (record : t) : list byte :=
      IncomingMessagesHeader31.encode (incoming_messages_header record) ++
      encode_bytes 2 (group record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 8 (cancelled_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match IncomingMessagesHeader31.decode bytes with
      | None => None
      | Some (incoming_messages_header_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (cancelled_order_id_value, bytes) =>
                      Some ({| incoming_messages_header := incoming_messages_header_value; group := group_value; instrument := instrument_value; cancelled_order_id := cancelled_order_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !IncomingMessagesHeader31.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite IncomingMessagesHeader31.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IncomingMessagesHeader31.eq_dec]. Defined.

  End OrderCancellation.

End MxSolaOrderEntryV121Firm.
