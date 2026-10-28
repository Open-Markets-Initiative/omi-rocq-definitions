From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Qatar Stock Exchange Qse Cash Market Data

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
  *)

Module QseCashMarketDataV26.

  Module PacketHeader.

    (** All messages contain a common packet header, so that a client implements line level protocol processing once and then develops parsing algorithms only for its choice of message *)
    Record t := {
      packet_length : N;
      packet_type : N;
      packet_sequence_number : N;
      send_time : N;
      service_id : N;
      delivery_flag : N;
      number_msg_entries : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_type record < 256 ^ N.of_nat 2)%N /\
      (packet_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 4)%N /\
      (service_id record < 256 ^ N.of_nat 2)%N /\
      (delivery_flag record < 256 ^ N.of_nat 1)%N /\
      (number_msg_entries record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_uint 2 (packet_type record) ++
      encode_uint 4 (packet_sequence_number record) ++
      encode_uint 4 (send_time record) ++
      encode_uint 2 (service_id record) ++
      encode_uint 1 (delivery_flag record) ++
      encode_uint 1 (number_msg_entries record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (packet_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (packet_sequence_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (send_time_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (service_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (delivery_flag_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (number_msg_entries_value, bytes) =>
                                  Some ({| packet_length := packet_length_value; packet_type := packet_type_value; packet_sequence_number := packet_sequence_number_value; send_time := send_time_value; service_id := service_id_value; delivery_flag := delivery_flag_value; number_msg_entries := number_msg_entries_value |}, bytes)
                              end
                          end
                      end
                  end
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  Module StockStateChangeMessage.

    (** A Stock State Change message is generated by the trading engines to announce a change in the state of an instrument. *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      filler_binary_int_2 : N;
      start_date_halting : list byte;
      start_time_halting : list byte;
      prog_opening_time : list byte;
      order_entry_rejection : list byte;
      instrument_state : list byte;
      instrument_trading_status : list byte;
      halt_reason : list byte;
      action_affecting_state : list byte;
      instrument_state_tcs : list byte;
      period_side : list byte;
      filler_binary_int_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (filler_binary_int_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (start_date_halting record) = 8 /\
      Datatypes.length (start_time_halting record) = 6 /\
      Datatypes.length (prog_opening_time record) = 6 /\
      Datatypes.length (order_entry_rejection record) = 1 /\
      Datatypes.length (instrument_state record) = 1 /\
      Datatypes.length (instrument_trading_status record) = 1 /\
      Datatypes.length (halt_reason record) = 1 /\
      Datatypes.length (action_affecting_state record) = 1 /\
      Datatypes.length (instrument_state_tcs record) = 1 /\
      Datatypes.length (period_side record) = 1 /\
      (filler_binary_int_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (filler_binary_int_2 record) ++
      encode_bytes 8 (start_date_halting record) ++
      encode_bytes 6 (start_time_halting record) ++
      encode_bytes 6 (prog_opening_time record) ++
      encode_bytes 1 (order_entry_rejection record) ++
      encode_bytes 1 (instrument_state record) ++
      encode_bytes 1 (instrument_trading_status record) ++
      encode_bytes 1 (halt_reason record) ++
      encode_bytes 1 (action_affecting_state record) ++
      encode_bytes 1 (instrument_state_tcs record) ++
      encode_bytes 1 (period_side record) ++
      encode_uint 1 (filler_binary_int_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (system_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (source_time_micro_secs_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (filler_binary_int_2_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (start_date_halting_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (start_time_halting_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (prog_opening_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (order_entry_rejection_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (instrument_state_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (instrument_trading_status_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (halt_reason_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (action_affecting_state_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (instrument_state_tcs_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (period_side_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (filler_binary_int_1_value, bytes) =>
                                                                          Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; filler_binary_int_2 := filler_binary_int_2_value; start_date_halting := start_date_halting_value; start_time_halting := start_time_halting_value; prog_opening_time := prog_opening_time_value; order_entry_rejection := order_entry_rejection_value; instrument_state := instrument_state_value; instrument_trading_status := instrument_trading_status_value; halt_reason := halt_reason_value; action_affecting_state := action_affecting_state_value; instrument_state_tcs := instrument_state_tcs_value; period_side := period_side_value; filler_binary_int_1 := filler_binary_int_1_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockStateChangeMessage.

  Module ClassStateChangeMessage.

    (** A Class State Change message announces a change in the trading market phase of a class or instrument group, which instruments belonging to it inherit. *)
    Record t := {
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      instrument_group_code : list byte;
      instrument_group_state : list byte;
      session_type : list byte;
      filler_binary_int_1 : N;
      class_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (instrument_group_code record) = 3 /\
      Datatypes.length (instrument_group_state record) = 1 /\
      Datatypes.length (session_type record) = 1 /\
      (filler_binary_int_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (class_state record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 3 (instrument_group_code record) ++
      encode_bytes 1 (instrument_group_state record) ++
      encode_bytes 1 (session_type record) ++
      encode_uint 1 (filler_binary_int_1 record) ++
      encode_bytes 4 (class_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (system_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (source_time_micro_secs_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (instrument_group_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (instrument_group_state_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (session_type_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (filler_binary_int_1_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (class_state_value, bytes) =>
                                          Some ({| source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; instrument_group_code := instrument_group_code_value; instrument_group_state := instrument_group_state_value; session_type := session_type_value; filler_binary_int_1 := filler_binary_int_1_value; class_state := class_state_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClassStateChangeMessage.

  Module MailMessage.

    (** A Mail message carries a free text notice broadcast to market participants. *)
    Record t := {
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      e_mail_msg_number : N;
      number_of_message : N;
      sequence_number : N;
      instrument_group_code : list byte;
      filler_ascii_str_1 : N;
      priority_indicator : list byte;
      type_of_message : list byte;
      address_type : list byte;
      title : list byte;
      text : list byte;
      filler_ascii_str_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (e_mail_msg_number record < 256 ^ N.of_nat 2)%N /\
      (number_of_message record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (instrument_group_code record) = 3 /\
      (filler_ascii_str_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (priority_indicator record) = 1 /\
      Datatypes.length (type_of_message record) = 1 /\
      Datatypes.length (address_type record) = 2 /\
      Datatypes.length (title record) = 80 /\
      Datatypes.length (text record) = 854 /\
      (filler_ascii_str_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (e_mail_msg_number record) ++
      encode_uint 2 (number_of_message record) ++
      encode_uint 2 (sequence_number record) ++
      encode_bytes 3 (instrument_group_code record) ++
      encode_uint 1 (filler_ascii_str_1 record) ++
      encode_bytes 1 (priority_indicator record) ++
      encode_bytes 1 (type_of_message record) ++
      encode_bytes 2 (address_type record) ++
      encode_bytes 80 (title record) ++
      encode_bytes 854 (text record) ++
      encode_uint 2 (filler_ascii_str_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (system_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (source_time_micro_secs_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (e_mail_msg_number_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (number_of_message_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (sequence_number_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (instrument_group_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (filler_ascii_str_1_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (priority_indicator_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (type_of_message_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (address_type_value, bytes) =>
                                                      match decode_bytes 80 bytes with
                                                      | None => None
                                                      | Some (title_value, bytes) =>
                                                          match decode_bytes 854 bytes with
                                                          | None => None
                                                          | Some (text_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (filler_ascii_str_2_value, bytes) =>
                                                                  Some ({| source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; e_mail_msg_number := e_mail_msg_number_value; number_of_message := number_of_message_value; sequence_number := sequence_number_value; instrument_group_code := instrument_group_code_value; filler_ascii_str_1 := filler_ascii_str_1_value; priority_indicator := priority_indicator_value; type_of_message := type_of_message_value; address_type := address_type_value; title := title_value; text := text_value; filler_ascii_str_2 := filler_ascii_str_2_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 964.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MailMessage.

  Module IndicativeMatchingPriceMessage.

    (** An Indicative Matching Price message gives the price at which the instrument would open, were the opening to occur at this moment. *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      im_price : N;
      variation : N;
      system_id : N;
      source_time_micro_secs : N;
      price_scale_code : N;
      variation_scale_code : N;
      im_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (im_price record < 256 ^ N.of_nat 4)%N /\
      (variation record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N /\
      (im_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (im_price record) ++
      encode_uint 4 (variation record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 1 (variation_scale_code record) ++
      encode_uint 4 (im_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (im_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (variation_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (system_id_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (source_time_micro_secs_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (price_scale_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (variation_scale_code_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (im_volume_value, bytes) =>
                                              Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; im_price := im_price_value; variation := variation_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; price_scale_code := price_scale_code_value; variation_scale_code := variation_scale_code_value; im_volume := im_volume_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End IndicativeMatchingPriceMessage.

  Module CollarsMessage.

    (** A Collars message gives the upper and lower price thresholds beyond which an instrument is reserved. *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      high_collar : N;
      low_collar : N;
      system_id : N;
      source_time_micro_secs : N;
      high_scale_code : N;
      low_scale_code : N;
      collar_type : list byte;
      filler_ascii_str_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (high_collar record < 256 ^ N.of_nat 4)%N /\
      (low_collar record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (high_scale_code record < 256 ^ N.of_nat 1)%N /\
      (low_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (collar_type record) = 1 /\
      (filler_ascii_str_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (high_collar record) ++
      encode_uint 4 (low_collar record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (high_scale_code record) ++
      encode_uint 1 (low_scale_code record) ++
      encode_bytes 1 (collar_type record) ++
      encode_uint 3 (filler_ascii_str_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (high_collar_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (low_collar_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (system_id_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (source_time_micro_secs_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (high_scale_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (low_scale_code_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (collar_type_value, bytes) =>
                                              match decode_uint 3 bytes with
                                              | None => None
                                              | Some (filler_ascii_str_3_value, bytes) =>
                                                  Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; high_collar := high_collar_value; low_collar := low_collar_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; high_scale_code := high_scale_code_value; low_scale_code := low_scale_code_value; collar_type := collar_type_value; filler_ascii_str_3 := filler_ascii_str_3_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CollarsMessage.

  Module SessionTimetableMessage.

    (** A Session Timetable message gives the timetable of the trading session for a group of instruments. *)
    Record t := {
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      instrument_group_code : list byte;
      session_type : list byte;
      time_pre_opening_1 : list byte;
      time_opening_1 : list byte;
      time_closing_1 : list byte;
      time_pre_opening_2 : list byte;
      time_opening_2 : list byte;
      time_closing_2 : list byte;
      time_pre_opening_3 : list byte;
      time_opening_3 : list byte;
      time_closing_3 : list byte;
      eod_time : list byte;
      filler_ascii_str_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (instrument_group_code record) = 3 /\
      Datatypes.length (session_type record) = 1 /\
      Datatypes.length (time_pre_opening_1 record) = 6 /\
      Datatypes.length (time_opening_1 record) = 6 /\
      Datatypes.length (time_closing_1 record) = 6 /\
      Datatypes.length (time_pre_opening_2 record) = 6 /\
      Datatypes.length (time_opening_2 record) = 6 /\
      Datatypes.length (time_closing_2 record) = 6 /\
      Datatypes.length (time_pre_opening_3 record) = 6 /\
      Datatypes.length (time_opening_3 record) = 6 /\
      Datatypes.length (time_closing_3 record) = 6 /\
      Datatypes.length (eod_time record) = 6 /\
      (filler_ascii_str_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 3 (instrument_group_code record) ++
      encode_bytes 1 (session_type record) ++
      encode_bytes 6 (time_pre_opening_1 record) ++
      encode_bytes 6 (time_opening_1 record) ++
      encode_bytes 6 (time_closing_1 record) ++
      encode_bytes 6 (time_pre_opening_2 record) ++
      encode_bytes 6 (time_opening_2 record) ++
      encode_bytes 6 (time_closing_2 record) ++
      encode_bytes 6 (time_pre_opening_3 record) ++
      encode_bytes 6 (time_opening_3 record) ++
      encode_bytes 6 (time_closing_3 record) ++
      encode_bytes 6 (eod_time record) ++
      encode_uint 2 (filler_ascii_str_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (system_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (source_time_micro_secs_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (instrument_group_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (session_type_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (time_pre_opening_1_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (time_opening_1_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (time_closing_1_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (time_pre_opening_2_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (time_opening_2_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (time_closing_2_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (time_pre_opening_3_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (time_opening_3_value, bytes) =>
                                                              match decode_bytes 6 bytes with
                                                              | None => None
                                                              | Some (time_closing_3_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (eod_time_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (filler_ascii_str_2_value, bytes) =>
                                                                          Some ({| source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; instrument_group_code := instrument_group_code_value; session_type := session_type_value; time_pre_opening_1 := time_pre_opening_1_value; time_opening_1 := time_opening_1_value; time_closing_1 := time_closing_1_value; time_pre_opening_2 := time_pre_opening_2_value; time_opening_2 := time_opening_2_value; time_closing_2 := time_closing_2_value; time_pre_opening_3 := time_pre_opening_3_value; time_opening_3 := time_opening_3_value; time_closing_3 := time_closing_3_value; eod_time := eod_time_value; filler_ascii_str_2 := filler_ascii_str_2_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
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
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SessionTimetableMessage.

  Module GlobalMarketActivitySummaryMessage.

    (** A Global Market Activity Summary message provides an overall summary of the global market activity. This message is used only at Qatar Exchange. *)
    Record t := {
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      nb_trades : N;
      qty_shares : N;
      amount_traded : N;
      price_scale_code : N;
      filler_ascii_str_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (nb_trades record < 256 ^ N.of_nat 4)%N /\
      (qty_shares record < 256 ^ N.of_nat 4)%N /\
      (amount_traded record < 256 ^ N.of_nat 4)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (filler_ascii_str_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 4 (nb_trades record) ++
      encode_uint 4 (qty_shares record) ++
      encode_uint 4 (amount_traded record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 3 (filler_ascii_str_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (system_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (source_time_micro_secs_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (nb_trades_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (qty_shares_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (amount_traded_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (price_scale_code_value, bytes) =>
                                      match decode_uint 3 bytes with
                                      | None => None
                                      | Some (filler_ascii_str_3_value, bytes) =>
                                          Some ({| source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; nb_trades := nb_trades_value; qty_shares := qty_shares_value; amount_traded := amount_traded_value; price_scale_code := price_scale_code_value; filler_ascii_str_3 := filler_ascii_str_3_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GlobalMarketActivitySummaryMessage.

  Module StartReferentialMessage.

    (** A Start Referential message marks the beginning of the broadcast of the reference data. *)
    Record t := {
      indicator : list byte;
      filler_ascii_str_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (indicator record) = 1 /\
      (filler_ascii_str_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (indicator record) ++
      encode_uint 3 (filler_ascii_str_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (indicator_value, bytes) =>
          match decode_uint 3 bytes with
          | None => None
          | Some (filler_ascii_str_3_value, bytes) =>
              Some ({| indicator := indicator_value; filler_ascii_str_3 := filler_ascii_str_3_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End StartReferentialMessage.

  Module EndReferentialMessage.

    (** An End Referential message marks the end of the broadcast of the reference data. *)
    Record t := {
      indicator : list byte;
      filler_ascii_str_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (indicator record) = 1 /\
      (filler_ascii_str_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (indicator record) ++
      encode_uint 3 (filler_ascii_str_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (indicator_value, bytes) =>
          match decode_uint 3 bytes with
          | None => None
          | Some (filler_ascii_str_3_value, bytes) =>
              Some ({| indicator := indicator_value; filler_ascii_str_3 := filler_ascii_str_3_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End EndReferentialMessage.

  Module ReferentialMessage.

    (** A Referential message carries the characteristics of an instrument, including its standard identifiers, trading parameters and reference prices. *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      last_adj_price : N;
      system_id : N;
      prev_volume_traded : N;
      fix_price_tick : N;
      source_time_micro_secs : N;
      stock_exchange_code : N;
      type_of_instrument : N;
      event_date : list byte;
      instrument_name : list byte;
      period_indicator : list byte;
      type_of_market_admission : list byte;
      issuing_country_code : list byte;
      trading_currency : list byte;
      instrument_group_code : list byte;
      instrument_category : list byte;
      instrument_code : list byte;
      date_of_last_trade : list byte;
      underlying_repo_isin_code : list byte;
      repo_expiry_date : list byte;
      first_settlement_date : list byte;
      type_of_derivatives : list byte;
      bic_depositary : list byte;
      icb : list byte;
      mic : list byte;
      underlying_wisin_code : list byte;
      depositary_list : list byte;
      main_depositary : list byte;
      type_of_corporate_event : list byte;
      time_lag_euronext_utc : list byte;
      time_lag_mi_fid_reg_utc : list byte;
      cfi : list byte;
      quantity_notation : list byte;
      index_set_of_var_price_tick : list byte;
      market_feed_code : list byte;
      mic_list : list byte;
      industry_code : list byte;
      industry_text : list byte;
      financial_market_code : list byte;
      us_indicators : list byte;
      filler_ascii_str_2 : N;
      prev_day_capital_traded : N;
      nom_mkt_price : N;
      lot_size : N;
      number_instrument_circ : N;
      shares_out : N;
      auth_shares : N;
      heading_number : N;
      section_number : N;
      repo_indicator : list byte;
      last_adj_price_scale_code : N;
      type_of_unit_exp : N;
      market_indicator : N;
      prev_day_capital_traded_scale_code : N;
      tax_code : N;
      nom_mkdt_price_scale_code : N;
      lot_size_scale_code : N;
      fix_price_tick_scale_code : N;
      mnemo : list byte;
      trading_code : list byte;
      filler_ascii_str_3 : N;
      strike_price : N;
      strike_currency : list byte;
      strike_scale_code : N;
      currency_coef : N;
      currency_coef_scale_code : N;
      trading_currency_indicator : N;
      strike_currency_indicator : N;
      market_segment : list byte;
      algo : list byte;
      local_name : list byte;
      small_trade : N;
      filler_binary_int_12 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (last_adj_price record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (prev_volume_traded record < 256 ^ N.of_nat 4)%N /\
      (fix_price_tick record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (stock_exchange_code record < 256 ^ N.of_nat 2)%N /\
      (type_of_instrument record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (event_date record) = 8 /\
      Datatypes.length (instrument_name record) = 18 /\
      Datatypes.length (period_indicator record) = 1 /\
      Datatypes.length (type_of_market_admission record) = 1 /\
      Datatypes.length (issuing_country_code record) = 3 /\
      Datatypes.length (trading_currency record) = 3 /\
      Datatypes.length (instrument_group_code record) = 3 /\
      Datatypes.length (instrument_category record) = 1 /\
      Datatypes.length (instrument_code record) = 12 /\
      Datatypes.length (date_of_last_trade record) = 8 /\
      Datatypes.length (underlying_repo_isin_code record) = 12 /\
      Datatypes.length (repo_expiry_date record) = 8 /\
      Datatypes.length (first_settlement_date record) = 8 /\
      Datatypes.length (type_of_derivatives record) = 1 /\
      Datatypes.length (bic_depositary record) = 11 /\
      Datatypes.length (icb record) = 4 /\
      Datatypes.length (mic record) = 4 /\
      Datatypes.length (underlying_wisin_code record) = 12 /\
      Datatypes.length (depositary_list record) = 25 /\
      Datatypes.length (main_depositary record) = 5 /\
      Datatypes.length (type_of_corporate_event record) = 2 /\
      Datatypes.length (time_lag_euronext_utc record) = 5 /\
      Datatypes.length (time_lag_mi_fid_reg_utc record) = 5 /\
      Datatypes.length (cfi record) = 6 /\
      Datatypes.length (quantity_notation record) = 4 /\
      Datatypes.length (index_set_of_var_price_tick record) = 2 /\
      Datatypes.length (market_feed_code record) = 2 /\
      Datatypes.length (mic_list record) = 24 /\
      Datatypes.length (industry_code record) = 4 /\
      Datatypes.length (industry_text record) = 100 /\
      Datatypes.length (financial_market_code record) = 3 /\
      Datatypes.length (us_indicators record) = 7 /\
      (filler_ascii_str_2 record < 256 ^ N.of_nat 2)%N /\
      (prev_day_capital_traded record < 256 ^ N.of_nat 8)%N /\
      (nom_mkt_price record < 256 ^ N.of_nat 8)%N /\
      (lot_size record < 256 ^ N.of_nat 8)%N /\
      (number_instrument_circ record < 256 ^ N.of_nat 8)%N /\
      (shares_out record < 256 ^ N.of_nat 8)%N /\
      (auth_shares record < 256 ^ N.of_nat 8)%N /\
      (heading_number record < 256 ^ N.of_nat 2)%N /\
      (section_number record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (repo_indicator record) = 1 /\
      (last_adj_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (type_of_unit_exp record < 256 ^ N.of_nat 1)%N /\
      (market_indicator record < 256 ^ N.of_nat 1)%N /\
      (prev_day_capital_traded_scale_code record < 256 ^ N.of_nat 1)%N /\
      (tax_code record < 256 ^ N.of_nat 1)%N /\
      (nom_mkdt_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (lot_size_scale_code record < 256 ^ N.of_nat 1)%N /\
      (fix_price_tick_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mnemo record) = 5 /\
      Datatypes.length (trading_code record) = 12 /\
      (filler_ascii_str_3 record < 256 ^ N.of_nat 3)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (strike_currency record) = 3 /\
      (strike_scale_code record < 256 ^ N.of_nat 1)%N /\
      (currency_coef record < 256 ^ N.of_nat 4)%N /\
      (currency_coef_scale_code record < 256 ^ N.of_nat 1)%N /\
      (trading_currency_indicator record < 256 ^ N.of_nat 1)%N /\
      (strike_currency_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_segment record) = 2 /\
      Datatypes.length (algo record) = 1 /\
      Datatypes.length (local_name record) = 30 /\
      (small_trade record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (filler_binary_int_12 record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (last_adj_price record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 4 (prev_volume_traded record) ++
      encode_uint 4 (fix_price_tick record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (stock_exchange_code record) ++
      encode_uint 2 (type_of_instrument record) ++
      encode_bytes 8 (event_date record) ++
      encode_bytes 18 (instrument_name record) ++
      encode_bytes 1 (period_indicator record) ++
      encode_bytes 1 (type_of_market_admission record) ++
      encode_bytes 3 (issuing_country_code record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_bytes 3 (instrument_group_code record) ++
      encode_bytes 1 (instrument_category record) ++
      encode_bytes 12 (instrument_code record) ++
      encode_bytes 8 (date_of_last_trade record) ++
      encode_bytes 12 (underlying_repo_isin_code record) ++
      encode_bytes 8 (repo_expiry_date record) ++
      encode_bytes 8 (first_settlement_date record) ++
      encode_bytes 1 (type_of_derivatives record) ++
      encode_bytes 11 (bic_depositary record) ++
      encode_bytes 4 (icb record) ++
      encode_bytes 4 (mic record) ++
      encode_bytes 12 (underlying_wisin_code record) ++
      encode_bytes 25 (depositary_list record) ++
      encode_bytes 5 (main_depositary record) ++
      encode_bytes 2 (type_of_corporate_event record) ++
      encode_bytes 5 (time_lag_euronext_utc record) ++
      encode_bytes 5 (time_lag_mi_fid_reg_utc record) ++
      encode_bytes 6 (cfi record) ++
      encode_bytes 4 (quantity_notation record) ++
      encode_bytes 2 (index_set_of_var_price_tick record) ++
      encode_bytes 2 (market_feed_code record) ++
      encode_bytes 24 (mic_list record) ++
      encode_bytes 4 (industry_code record) ++
      encode_bytes 100 (industry_text record) ++
      encode_bytes 3 (financial_market_code record) ++
      encode_bytes 7 (us_indicators record) ++
      encode_uint 2 (filler_ascii_str_2 record) ++
      encode_uint 8 (prev_day_capital_traded record) ++
      encode_uint 8 (nom_mkt_price record) ++
      encode_uint 8 (lot_size record) ++
      encode_uint 8 (number_instrument_circ record) ++
      encode_uint 8 (shares_out record) ++
      encode_uint 8 (auth_shares record) ++
      encode_uint 2 (heading_number record) ++
      encode_uint 1 (section_number record) ++
      encode_bytes 1 (repo_indicator record) ++
      encode_uint 1 (last_adj_price_scale_code record) ++
      encode_uint 1 (type_of_unit_exp record) ++
      encode_uint 1 (market_indicator record) ++
      encode_uint 1 (prev_day_capital_traded_scale_code record) ++
      encode_uint 1 (tax_code record) ++
      encode_uint 1 (nom_mkdt_price_scale_code record) ++
      encode_uint 1 (lot_size_scale_code record) ++
      encode_uint 1 (fix_price_tick_scale_code record) ++
      encode_bytes 5 (mnemo record) ++
      encode_bytes 12 (trading_code record) ++
      encode_uint 3 (filler_ascii_str_3 record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 3 (strike_currency record) ++
      encode_uint 1 (strike_scale_code record) ++
      encode_uint 4 (currency_coef record) ++
      encode_uint 1 (currency_coef_scale_code record) ++
      encode_uint 1 (trading_currency_indicator record) ++
      encode_uint 1 (strike_currency_indicator record) ++
      encode_bytes 2 (market_segment record) ++
      encode_bytes 1 (algo record) ++
      encode_bytes 30 (local_name record) ++
      encode_uint 4 (small_trade record) ++
      encode_bytes 12 (filler_binary_int_12 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (last_adj_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (system_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (prev_volume_traded_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (fix_price_tick_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (source_time_micro_secs_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (stock_exchange_code_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (type_of_instrument_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (event_date_value, bytes) =>
                                                  match decode_bytes 18 bytes with
                                                  | None => None
                                                  | Some (instrument_name_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (period_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (type_of_market_admission_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (issuing_country_code_value, bytes) =>
                                                                  match decode_bytes 3 bytes with
                                                                  | None => None
                                                                  | Some (trading_currency_value, bytes) =>
                                                                      match decode_bytes 3 bytes with
                                                                      | None => None
                                                                      | Some (instrument_group_code_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (instrument_category_value, bytes) =>
                                                                              match decode_bytes 12 bytes with
                                                                              | None => None
                                                                              | Some (instrument_code_value, bytes) =>
                                                                                  match decode_bytes 8 bytes with
                                                                                  | None => None
                                                                                  | Some (date_of_last_trade_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (underlying_repo_isin_code_value, bytes) =>
                                                                                          match decode_bytes 8 bytes with
                                                                                          | None => None
                                                                                          | Some (repo_expiry_date_value, bytes) =>
                                                                                              match decode_bytes 8 bytes with
                                                                                              | None => None
                                                                                              | Some (first_settlement_date_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (type_of_derivatives_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bic_depositary_value, bytes) =>
                                                                                                          match decode_bytes 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (icb_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (mic_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (underlying_wisin_code_value, bytes) =>
                                                                                                                      match decode_bytes 25 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (depositary_list_value, bytes) =>
                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (main_depositary_value, bytes) =>
                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (type_of_corporate_event_value, bytes) =>
                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (time_lag_euronext_utc_value, bytes) =>
                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (time_lag_mi_fid_reg_utc_value, bytes) =>
                                                                                                                                          match decode_bytes 6 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (cfi_value, bytes) =>
                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (quantity_notation_value, bytes) =>
                                                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (index_set_of_var_price_tick_value, bytes) =>
                                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (market_feed_code_value, bytes) =>
                                                                                                                                                          match decode_bytes 24 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (mic_list_value, bytes) =>
                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (industry_code_value, bytes) =>
                                                                                                                                                                  match decode_bytes 100 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (industry_text_value, bytes) =>
                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (financial_market_code_value, bytes) =>
                                                                                                                                                                          match decode_bytes 7 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (us_indicators_value, bytes) =>
                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (filler_ascii_str_2_value, bytes) =>
                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (prev_day_capital_traded_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (nom_mkt_price_value, bytes) =>
                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (lot_size_value, bytes) =>
                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (number_instrument_circ_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (shares_out_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (auth_shares_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (heading_number_value, bytes) =>
                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (section_number_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (repo_indicator_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (last_adj_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (type_of_unit_exp_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (market_indicator_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (prev_day_capital_traded_scale_code_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (tax_code_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (nom_mkdt_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (lot_size_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (fix_price_tick_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (mnemo_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (trading_code_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint 3 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (filler_ascii_str_3_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (strike_currency_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (strike_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (currency_coef_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (currency_coef_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (trading_currency_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (strike_currency_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (market_segment_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (algo_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 30 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (local_name_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (small_trade_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (filler_binary_int_12_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; last_adj_price := last_adj_price_value; system_id := system_id_value; prev_volume_traded := prev_volume_traded_value; fix_price_tick := fix_price_tick_value; source_time_micro_secs := source_time_micro_secs_value; stock_exchange_code := stock_exchange_code_value; type_of_instrument := type_of_instrument_value; event_date := event_date_value; instrument_name := instrument_name_value; period_indicator := period_indicator_value; type_of_market_admission := type_of_market_admission_value; issuing_country_code := issuing_country_code_value; trading_currency := trading_currency_value; instrument_group_code := instrument_group_code_value; instrument_category := instrument_category_value; instrument_code := instrument_code_value; date_of_last_trade := date_of_last_trade_value; underlying_repo_isin_code := underlying_repo_isin_code_value; repo_expiry_date := repo_expiry_date_value; first_settlement_date := first_settlement_date_value; type_of_derivatives := type_of_derivatives_value; bic_depositary := bic_depositary_value; icb := icb_value; mic := mic_value; underlying_wisin_code := underlying_wisin_code_value; depositary_list := depositary_list_value; main_depositary := main_depositary_value; type_of_corporate_event := type_of_corporate_event_value; time_lag_euronext_utc := time_lag_euronext_utc_value; time_lag_mi_fid_reg_utc := time_lag_mi_fid_reg_utc_value; cfi := cfi_value; quantity_notation := quantity_notation_value; index_set_of_var_price_tick := index_set_of_var_price_tick_value; market_feed_code := market_feed_code_value; mic_list := mic_list_value; industry_code := industry_code_value; industry_text := industry_text_value; financial_market_code := financial_market_code_value; us_indicators := us_indicators_value; filler_ascii_str_2 := filler_ascii_str_2_value; prev_day_capital_traded := prev_day_capital_traded_value; nom_mkt_price := nom_mkt_price_value; lot_size := lot_size_value; number_instrument_circ := number_instrument_circ_value; shares_out := shares_out_value; auth_shares := auth_shares_value; heading_number := heading_number_value; section_number := section_number_value; repo_indicator := repo_indicator_value; last_adj_price_scale_code := last_adj_price_scale_code_value; type_of_unit_exp := type_of_unit_exp_value; market_indicator := market_indicator_value; prev_day_capital_traded_scale_code := prev_day_capital_traded_scale_code_value; tax_code := tax_code_value; nom_mkdt_price_scale_code := nom_mkdt_price_scale_code_value; lot_size_scale_code := lot_size_scale_code_value; fix_price_tick_scale_code := fix_price_tick_scale_code_value; mnemo := mnemo_value; trading_code := trading_code_value; filler_ascii_str_3 := filler_ascii_str_3_value; strike_price := strike_price_value; strike_currency := strike_currency_value; strike_scale_code := strike_scale_code_value; currency_coef := currency_coef_value; currency_coef_scale_code := currency_coef_scale_code_value; trading_currency_indicator := trading_currency_indicator_value; strike_currency_indicator := strike_currency_indicator_value; market_segment := market_segment_value; algo := algo_value; local_name := local_name_value; small_trade := small_trade_value; filler_binary_int_12 := filler_binary_int_12_value |}, bytes)
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 492.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 bound_74]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_uint by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_uint by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_uint by exact bound_65.
      rewrite decode_encode_uint by exact bound_66.
      rewrite decode_encode_uint by exact bound_67.
      rewrite decode_encode_uint by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      rewrite decode_encode_bytes by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReferentialMessage.

  Module TradeCreationMessage.

    (** A Trade Creation message announces a trade that has just been created in the trading engine. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      trade_id_number : N;
      quote_link_id : N;
      source_seq_num : N;
      price : N;
      volume : N;
      system_id : N;
      source_time_micro_secs : N;
      small_trade_indicator : list byte;
      trad_cond_2 : list byte;
      trad_cond_3 : list byte;
      trade_origin : list byte;
      opening_trade_indicator : list byte;
      price_scale_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (trade_id_number record < 256 ^ N.of_nat 4)%N /\
      (quote_link_id record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (small_trade_indicator record) = 1 /\
      Datatypes.length (trad_cond_2 record) = 1 /\
      Datatypes.length (trad_cond_3 record) = 1 /\
      Datatypes.length (trade_origin record) = 1 /\
      Datatypes.length (opening_trade_indicator record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (trade_id_number record) ++
      encode_uint 4 (quote_link_id record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 1 (small_trade_indicator record) ++
      encode_bytes 1 (trad_cond_2 record) ++
      encode_bytes 1 (trad_cond_3 record) ++
      encode_bytes 1 (trade_origin record) ++
      encode_bytes 1 (opening_trade_indicator record) ++
      encode_uint 1 (price_scale_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_id_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quote_link_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (source_seq_num_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (system_id_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (source_time_micro_secs_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (small_trade_indicator_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trad_cond_2_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trad_cond_3_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_origin_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (opening_trade_indicator_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (price_scale_code_value, bytes) =>
                                                                  Some ({| symbol_index := symbol_index_value; source_time := source_time_value; trade_id_number := trade_id_number_value; quote_link_id := quote_link_id_value; source_seq_num := source_seq_num_value; price := price_value; volume := volume_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; small_trade_indicator := small_trade_indicator_value; trad_cond_2 := trad_cond_2_value; trad_cond_3 := trad_cond_3_value; trade_origin := trade_origin_value; opening_trade_indicator := opening_trade_indicator_value; price_scale_code := price_scale_code_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCreationMessage.

  Module TradeCancellationMessage.

    (** A Trade Cancellation message announces the cancellation of a trade previously published. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      original_trade_id_number : N;
      system_id : N;
      source_time_micro_secs : N;
      filler_binary_int_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id_number record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (filler_binary_int_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (original_trade_id_number record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (filler_binary_int_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_trade_id_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (system_id_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (source_time_micro_secs_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (filler_binary_int_2_value, bytes) =>
                                  Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; original_trade_id_number := original_trade_id_number_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; filler_binary_int_2 := filler_binary_int_2_value |}, bytes)
                              end
                          end
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

  End TradeCancellationMessage.

  Module TradeFullInformationMessage.

    (** A Trade Full Information message carries a trade along with the cumulated statistics of the instrument for the trading day. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      trade_id_number : N;
      quote_link_id : N;
      source_seq_num : N;
      price : N;
      volume : N;
      cumulative_quantity : N;
      highest_price : N;
      lowest_price : N;
      variation_last_price : N;
      system_id : N;
      source_time_micro_secs : N;
      filler_binary_int_2 : N;
      small_trade_indicator : list byte;
      trad_cond_2 : list byte;
      trad_cond_3 : list byte;
      trade_origin : list byte;
      tick_direction : list byte;
      opening_trade_indicator : list byte;
      variation_scale_code : N;
      price_scale_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (trade_id_number record < 256 ^ N.of_nat 4)%N /\
      (quote_link_id record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (cumulative_quantity record < 256 ^ N.of_nat 4)%N /\
      (highest_price record < 256 ^ N.of_nat 4)%N /\
      (lowest_price record < 256 ^ N.of_nat 4)%N /\
      (variation_last_price record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (filler_binary_int_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (small_trade_indicator record) = 1 /\
      Datatypes.length (trad_cond_2 record) = 1 /\
      Datatypes.length (trad_cond_3 record) = 1 /\
      Datatypes.length (trade_origin record) = 1 /\
      Datatypes.length (tick_direction record) = 1 /\
      Datatypes.length (opening_trade_indicator record) = 1 /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (trade_id_number record) ++
      encode_uint 4 (quote_link_id record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (cumulative_quantity record) ++
      encode_uint 4 (highest_price record) ++
      encode_uint 4 (lowest_price record) ++
      encode_uint 4 (variation_last_price record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (filler_binary_int_2 record) ++
      encode_bytes 1 (small_trade_indicator record) ++
      encode_bytes 1 (trad_cond_2 record) ++
      encode_bytes 1 (trad_cond_3 record) ++
      encode_bytes 1 (trade_origin record) ++
      encode_bytes 1 (tick_direction record) ++
      encode_bytes 1 (opening_trade_indicator record) ++
      encode_uint 1 (variation_scale_code record) ++
      encode_uint 1 (price_scale_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_id_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quote_link_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (source_seq_num_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cumulative_quantity_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (highest_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (lowest_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (variation_last_price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (system_id_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (source_time_micro_secs_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (filler_binary_int_2_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (small_trade_indicator_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trad_cond_2_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (trad_cond_3_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (trade_origin_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (tick_direction_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (opening_trade_indicator_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (variation_scale_code_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (price_scale_code_value, bytes) =>
                                                                                              Some ({| symbol_index := symbol_index_value; source_time := source_time_value; trade_id_number := trade_id_number_value; quote_link_id := quote_link_id_value; source_seq_num := source_seq_num_value; price := price_value; volume := volume_value; cumulative_quantity := cumulative_quantity_value; highest_price := highest_price_value; lowest_price := lowest_price_value; variation_last_price := variation_last_price_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; filler_binary_int_2 := filler_binary_int_2_value; small_trade_indicator := small_trade_indicator_value; trad_cond_2 := trad_cond_2_value; trad_cond_3 := trad_cond_3_value; trade_origin := trade_origin_value; tick_direction := tick_direction_value; opening_trade_indicator := opening_trade_indicator_value; variation_scale_code := variation_scale_code_value; price_scale_code := price_scale_code_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeFullInformationMessage.

  Module PriceUpdateMessage.

    (** A Price Update message updates the statistics of an instrument without carrying a new trade. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      price : N;
      highest_price : N;
      lowest_price : N;
      variation_last_price : N;
      system_id : N;
      source_time_micro_secs : N;
      type_of_price : N;
      filler_binary_int_2 : N;
      price_scale_code : N;
      variation_scale_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (highest_price record < 256 ^ N.of_nat 4)%N /\
      (lowest_price record < 256 ^ N.of_nat 4)%N /\
      (variation_last_price record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (type_of_price record < 256 ^ N.of_nat 2)%N /\
      (filler_binary_int_2 record < 256 ^ N.of_nat 2)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (highest_price record) ++
      encode_uint 4 (lowest_price record) ++
      encode_uint 4 (variation_last_price record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (type_of_price record) ++
      encode_uint 2 (filler_binary_int_2 record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 1 (variation_scale_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (highest_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (lowest_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (variation_last_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (system_id_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (source_time_micro_secs_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (type_of_price_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (filler_binary_int_2_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (price_scale_code_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (variation_scale_code_value, bytes) =>
                                                          Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; price := price_value; highest_price := highest_price_value; lowest_price := lowest_price_value; variation_last_price := variation_last_price_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; type_of_price := type_of_price_value; filler_binary_int_2 := filler_binary_int_2_value; price_scale_code := price_scale_code_value; variation_scale_code := variation_scale_code_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End PriceUpdateMessage.

  Module AuctionSummaryMessage.

    (** An Auction Summary message summarises the trades resulting from an auction. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      first_price : N;
      last_price : N;
      highest_price : N;
      lowest_price : N;
      cumulative_quantity : N;
      variation : N;
      system_id : N;
      source_time_micro_secs : N;
      type_of_last_price : N;
      tick_direction : list byte;
      instrument_valuation_price : list byte;
      price_scale_code : N;
      variation_scale_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (first_price record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      (highest_price record < 256 ^ N.of_nat 4)%N /\
      (lowest_price record < 256 ^ N.of_nat 4)%N /\
      (cumulative_quantity record < 256 ^ N.of_nat 4)%N /\
      (variation record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (type_of_last_price record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (tick_direction record) = 1 /\
      Datatypes.length (instrument_valuation_price record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (first_price record) ++
      encode_uint 4 (last_price record) ++
      encode_uint 4 (highest_price record) ++
      encode_uint 4 (lowest_price record) ++
      encode_uint 4 (cumulative_quantity record) ++
      encode_uint 4 (variation record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (type_of_last_price record) ++
      encode_bytes 1 (tick_direction record) ++
      encode_bytes 1 (instrument_valuation_price record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 1 (variation_scale_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (first_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (last_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (highest_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (lowest_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cumulative_quantity_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (variation_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (system_id_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (source_time_micro_secs_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (type_of_last_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (tick_direction_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (instrument_valuation_price_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (price_scale_code_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (variation_scale_code_value, bytes) =>
                                                                      Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; first_price := first_price_value; last_price := last_price_value; highest_price := highest_price_value; lowest_price := lowest_price_value; cumulative_quantity := cumulative_quantity_value; variation := variation_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; type_of_last_price := type_of_last_price_value; tick_direction := tick_direction_value; instrument_valuation_price := instrument_valuation_price_value; price_scale_code := price_scale_code_value; variation_scale_code := variation_scale_code_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionSummaryMessage.

  Module VwapClosingPriceMessage.

    (** A VWAP - Closing Price message contains the real time Volume-Weighted Average Price for an instrument together with the current closing price. This message is used exclusively at Qatar Exchange. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      sending_indicator : N;
      closing_price_rule : N;
      closing_price : N;
      adjusted_closing_price : N;
      nb_trades : N;
      qty_shares : N;
      amount_traded : N;
      system_id : N;
      price_scale_code : N;
      filler_ascii_str_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_indicator record < 256 ^ N.of_nat 2)%N /\
      (closing_price_rule record < 256 ^ N.of_nat 2)%N /\
      (closing_price record < 256 ^ N.of_nat 4)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 4)%N /\
      (nb_trades record < 256 ^ N.of_nat 4)%N /\
      (qty_shares record < 256 ^ N.of_nat 4)%N /\
      (amount_traded record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (filler_ascii_str_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 2 (sending_indicator record) ++
      encode_uint 2 (closing_price_rule record) ++
      encode_uint 4 (closing_price record) ++
      encode_uint 4 (adjusted_closing_price record) ++
      encode_uint 4 (nb_trades record) ++
      encode_uint 4 (qty_shares record) ++
      encode_uint 4 (amount_traded record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 3 (filler_ascii_str_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (sending_indicator_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (closing_price_rule_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (closing_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (adjusted_closing_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (nb_trades_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (qty_shares_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (amount_traded_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (system_id_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (price_scale_code_value, bytes) =>
                                                      match decode_uint 3 bytes with
                                                      | None => None
                                                      | Some (filler_ascii_str_3_value, bytes) =>
                                                          Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; sending_indicator := sending_indicator_value; closing_price_rule := closing_price_rule_value; closing_price := closing_price_value; adjusted_closing_price := adjusted_closing_price_value; nb_trades := nb_trades_value; qty_shares := qty_shares_value; amount_traded := amount_traded_value; system_id := system_id_value; price_scale_code := price_scale_code_value; filler_ascii_str_3 := filler_ascii_str_3_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End VwapClosingPriceMessage.

  Module QuotesMessage.

    (** A Quotes message carries the best limits of the order book for an instrument. *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      quote_link_id : N;
      ask_price : N;
      ask_size : N;
      bid_price : N;
      bid_size : N;
      system_id : N;
      number_ask_orders : N;
      number_bid_orders : N;
      source_time_micro_secs : N;
      type_of_ask_price : N;
      type_of_bid_price : N;
      quote_condition : list byte;
      quote_number : N;
      price_scale_code : N;
      filler_ascii_str_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (quote_link_id record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (number_ask_orders record < 256 ^ N.of_nat 2)%N /\
      (number_bid_orders record < 256 ^ N.of_nat 2)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (type_of_ask_price record < 256 ^ N.of_nat 1)%N /\
      (type_of_bid_price record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (quote_number record < 256 ^ N.of_nat 1)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (filler_ascii_str_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (quote_link_id record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (ask_size record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (bid_size record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (number_ask_orders record) ++
      encode_uint 2 (number_bid_orders record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (type_of_ask_price record) ++
      encode_uint 1 (type_of_bid_price record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (quote_number record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 1 (filler_ascii_str_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quote_link_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ask_size_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bid_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (bid_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (system_id_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (number_ask_orders_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (number_bid_orders_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (source_time_micro_secs_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (type_of_ask_price_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (type_of_bid_price_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (quote_condition_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (quote_number_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (price_scale_code_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (filler_ascii_str_1_value, bytes) =>
                                                                              Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; quote_link_id := quote_link_id_value; ask_price := ask_price_value; ask_size := ask_size_value; bid_price := bid_price_value; bid_size := bid_size_value; system_id := system_id_value; number_ask_orders := number_ask_orders_value; number_bid_orders := number_bid_orders_value; source_time_micro_secs := source_time_micro_secs_value; type_of_ask_price := type_of_ask_price_value; type_of_bid_price := type_of_bid_price_value; quote_condition := quote_condition_value; quote_number := quote_number_value; price_scale_code := price_scale_code_value; filler_ascii_str_1 := filler_ascii_str_1_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuotesMessage.

  Module OrderUpdateMarketSheetMessage.

    (** An Order Update message carries a single order of the market sheet, so that the order book of an instrument may be rebuilt and maintained. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      price : N;
      aggregated_volume : N;
      volume : N;
      link_id : N;
      order_id : N;
      system_id : N;
      source_time_micro_secs : N;
      number_orders : N;
      side : list byte;
      order_type : list byte;
      action_type : list byte;
      price_scale_code : N;
      order_date : N;
      order_priority_date : N;
      order_priority_time : N;
      order_priority_micro_secs : N;
      order_origin : list byte;
      filler_binary_int_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (aggregated_volume record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (link_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (number_orders record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (action_type record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (order_date record < 256 ^ N.of_nat 4)%N /\
      (order_priority_date record < 256 ^ N.of_nat 4)%N /\
      (order_priority_time record < 256 ^ N.of_nat 4)%N /\
      (order_priority_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_origin record) = 1 /\
      (filler_binary_int_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (aggregated_volume record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (link_id record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (number_orders record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 1 (action_type record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 4 (order_date record) ++
      encode_uint 4 (order_priority_date record) ++
      encode_uint 4 (order_priority_time record) ++
      encode_uint 2 (order_priority_micro_secs record) ++
      encode_bytes 1 (order_origin record) ++
      encode_uint 1 (filler_binary_int_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (aggregated_volume_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (link_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (system_id_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (source_time_micro_secs_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (number_orders_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (side_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (order_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (action_type_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (price_scale_code_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (order_date_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (order_priority_date_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (order_priority_time_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (order_priority_micro_secs_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (order_origin_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (filler_binary_int_1_value, bytes) =>
                                                                                          Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; price := price_value; aggregated_volume := aggregated_volume_value; volume := volume_value; link_id := link_id_value; order_id := order_id_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; number_orders := number_orders_value; side := side_value; order_type := order_type_value; action_type := action_type_value; price_scale_code := price_scale_code_value; order_date := order_date_value; order_priority_date := order_priority_date_value; order_priority_time := order_priority_time_value; order_priority_micro_secs := order_priority_micro_secs_value; order_origin := order_origin_value; filler_binary_int_1 := filler_binary_int_1_value |}, bytes)
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderUpdateMarketSheetMessage.

  Module OrderbookRetransmissionDelimiterMessage.

    (** An Orderbook Retransmission Delimiter message delimits the retransmission of a market sheet, so that the order book is cleaned before the orders that follow are applied. *)
    Record t := {
      source_time : N;
      source_seq_num : N;
      trading_engine_id : list byte;
      instance_id : N;
      retransmission_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_engine_id record) = 2 /\
      (instance_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (retransmission_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_bytes 2 (trading_engine_id record) ++
      encode_uint 1 (instance_id record) ++
      encode_bytes 1 (retransmission_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_seq_num_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (trading_engine_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (instance_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (retransmission_indicator_value, bytes) =>
                          Some ({| source_time := source_time_value; source_seq_num := source_seq_num_value; trading_engine_id := trading_engine_id_value; instance_id := instance_id_value; retransmission_indicator := retransmission_indicator_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookRetransmissionDelimiterMessage.

  Module RealTimeIndexMessage.

    (** A Real Time Index message carries the current level of an index. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      index_level : N;
      forerunner_level : N;
      session_high : N;
      session_low : N;
      percentage_of_capitalization : N;
      variation_from_previous_days_price : N;
      system_id : N;
      source_time_micro_secs : N;
      num_of_securities_quoted : N;
      index_level_code : list byte;
      type_of_level : list byte;
      level_scale_code : N;
      percentage_scale_code : N;
      variation_scale_code : N;
      rebroadcast_indicator : list byte;
      filler_ascii_str_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (index_level record < 256 ^ N.of_nat 4)%N /\
      (forerunner_level record < 256 ^ N.of_nat 4)%N /\
      (session_high record < 256 ^ N.of_nat 4)%N /\
      (session_low record < 256 ^ N.of_nat 4)%N /\
      (percentage_of_capitalization record < 256 ^ N.of_nat 4)%N /\
      (variation_from_previous_days_price record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (num_of_securities_quoted record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (index_level_code record) = 1 /\
      Datatypes.length (type_of_level record) = 1 /\
      (level_scale_code record < 256 ^ N.of_nat 1)%N /\
      (percentage_scale_code record < 256 ^ N.of_nat 1)%N /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (rebroadcast_indicator record) = 1 /\
      (filler_ascii_str_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (index_level record) ++
      encode_uint 4 (forerunner_level record) ++
      encode_uint 4 (session_high record) ++
      encode_uint 4 (session_low record) ++
      encode_uint 4 (percentage_of_capitalization record) ++
      encode_uint 4 (variation_from_previous_days_price record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (num_of_securities_quoted record) ++
      encode_bytes 1 (index_level_code record) ++
      encode_bytes 1 (type_of_level record) ++
      encode_uint 1 (level_scale_code record) ++
      encode_uint 1 (percentage_scale_code record) ++
      encode_uint 1 (variation_scale_code record) ++
      encode_bytes 1 (rebroadcast_indicator record) ++
      encode_uint 2 (filler_ascii_str_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (index_level_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (forerunner_level_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (session_high_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (session_low_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (percentage_of_capitalization_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (variation_from_previous_days_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (system_id_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (source_time_micro_secs_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (num_of_securities_quoted_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (index_level_code_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (type_of_level_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (level_scale_code_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (percentage_scale_code_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (variation_scale_code_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (rebroadcast_indicator_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (filler_ascii_str_2_value, bytes) =>
                                                                              Some ({| symbol_index := symbol_index_value; source_time := source_time_value; index_level := index_level_value; forerunner_level := forerunner_level_value; session_high := session_high_value; session_low := session_low_value; percentage_of_capitalization := percentage_of_capitalization_value; variation_from_previous_days_price := variation_from_previous_days_price_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; num_of_securities_quoted := num_of_securities_quoted_value; index_level_code := index_level_code_value; type_of_level := type_of_level_value; level_scale_code := level_scale_code_value; percentage_scale_code := percentage_scale_code_value; variation_scale_code := variation_scale_code_value; rebroadcast_indicator := rebroadcast_indicator_value; filler_ascii_str_2 := filler_ascii_str_2_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RealTimeIndexMessage.

  Module IndexSummaryMessage.

    (** An Index Summary message gives the summary of an index for the trading day. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      preliminary_opening_level : N;
      preliminary_opening_time : N;
      first_level : N;
      first_time : N;
      opening_reference_level : N;
      opening_reference_time : N;
      closing_reference_level : N;
      closing_reference_time : N;
      percent_variation_prev_clos : N;
      high_level : N;
      high_time : N;
      low_level : N;
      low_time : N;
      clearing_level : N;
      clearing_time : N;
      liquidation_level : N;
      liquidation_time : N;
      system_id : N;
      source_time_micro_secs : N;
      type_of_level : list byte;
      level_scale_code : N;
      variation_scale_code : N;
      filler_ascii_str_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (preliminary_opening_level record < 256 ^ N.of_nat 4)%N /\
      (preliminary_opening_time record < 256 ^ N.of_nat 4)%N /\
      (first_level record < 256 ^ N.of_nat 4)%N /\
      (first_time record < 256 ^ N.of_nat 4)%N /\
      (opening_reference_level record < 256 ^ N.of_nat 4)%N /\
      (opening_reference_time record < 256 ^ N.of_nat 4)%N /\
      (closing_reference_level record < 256 ^ N.of_nat 4)%N /\
      (closing_reference_time record < 256 ^ N.of_nat 4)%N /\
      (percent_variation_prev_clos record < 256 ^ N.of_nat 4)%N /\
      (high_level record < 256 ^ N.of_nat 4)%N /\
      (high_time record < 256 ^ N.of_nat 4)%N /\
      (low_level record < 256 ^ N.of_nat 4)%N /\
      (low_time record < 256 ^ N.of_nat 4)%N /\
      (clearing_level record < 256 ^ N.of_nat 4)%N /\
      (clearing_time record < 256 ^ N.of_nat 4)%N /\
      (liquidation_level record < 256 ^ N.of_nat 4)%N /\
      (liquidation_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (type_of_level record) = 1 /\
      (level_scale_code record < 256 ^ N.of_nat 1)%N /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N /\
      (filler_ascii_str_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (preliminary_opening_level record) ++
      encode_uint 4 (preliminary_opening_time record) ++
      encode_uint 4 (first_level record) ++
      encode_uint 4 (first_time record) ++
      encode_uint 4 (opening_reference_level record) ++
      encode_uint 4 (opening_reference_time record) ++
      encode_uint 4 (closing_reference_level record) ++
      encode_uint 4 (closing_reference_time record) ++
      encode_uint 4 (percent_variation_prev_clos record) ++
      encode_uint 4 (high_level record) ++
      encode_uint 4 (high_time record) ++
      encode_uint 4 (low_level record) ++
      encode_uint 4 (low_time record) ++
      encode_uint 4 (clearing_level record) ++
      encode_uint 4 (clearing_time record) ++
      encode_uint 4 (liquidation_level record) ++
      encode_uint 4 (liquidation_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 1 (type_of_level record) ++
      encode_uint 1 (level_scale_code record) ++
      encode_uint 1 (variation_scale_code record) ++
      encode_uint 3 (filler_ascii_str_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (preliminary_opening_level_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (preliminary_opening_time_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (first_level_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (first_time_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (opening_reference_level_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (opening_reference_time_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (closing_reference_level_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (closing_reference_time_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (percent_variation_prev_clos_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (high_level_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (high_time_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (low_level_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (low_time_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (clearing_level_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (clearing_time_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (liquidation_level_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (liquidation_time_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (system_id_value, bytes) =>
                                                                                      match decode_uint 2 bytes with
                                                                                      | None => None
                                                                                      | Some (source_time_micro_secs_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (type_of_level_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (level_scale_code_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (variation_scale_code_value, bytes) =>
                                                                                                      match decode_uint 3 bytes with
                                                                                                      | None => None
                                                                                                      | Some (filler_ascii_str_3_value, bytes) =>
                                                                                                          Some ({| symbol_index := symbol_index_value; source_time := source_time_value; preliminary_opening_level := preliminary_opening_level_value; preliminary_opening_time := preliminary_opening_time_value; first_level := first_level_value; first_time := first_time_value; opening_reference_level := opening_reference_level_value; opening_reference_time := opening_reference_time_value; closing_reference_level := closing_reference_level_value; closing_reference_time := closing_reference_time_value; percent_variation_prev_clos := percent_variation_prev_clos_value; high_level := high_level_value; high_time := high_time_value; low_level := low_level_value; low_time := low_time_value; clearing_level := clearing_level_value; clearing_time := clearing_time_value; liquidation_level := liquidation_level_value; liquidation_time := liquidation_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; type_of_level := type_of_level_value; level_scale_code := level_scale_code_value; variation_scale_code := variation_scale_code_value; filler_ascii_str_3 := filler_ascii_str_3_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexSummaryMessage.

  Module IndexCompositionMessage.

    (** An Index Composition message transmits one instrument making up an index, its weight and its adjustment coefficient. *)
    Record t := {
      symbol_index : N;
      source_time : N;
      instrument_weight : N;
      instrument_factor : N;
      previous_close : N;
      system_id : N;
      source_time_micro_secs : N;
      number_of_conponents : N;
      instrument_id_of_component : list byte;
      mnemo : list byte;
      index_frequency : list byte;
      price_scale_code : N;
      level_scale_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (instrument_weight record < 256 ^ N.of_nat 4)%N /\
      (instrument_factor record < 256 ^ N.of_nat 4)%N /\
      (previous_close record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (number_of_conponents record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (instrument_id_of_component record) = 12 /\
      Datatypes.length (mnemo record) = 5 /\
      Datatypes.length (index_frequency record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (level_scale_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (instrument_weight record) ++
      encode_uint 4 (instrument_factor record) ++
      encode_uint 4 (previous_close record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (number_of_conponents record) ++
      encode_bytes 12 (instrument_id_of_component record) ++
      encode_bytes 5 (mnemo record) ++
      encode_bytes 1 (index_frequency record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 1 (level_scale_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_weight_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_factor_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (previous_close_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (system_id_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (source_time_micro_secs_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (number_of_conponents_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (instrument_id_of_component_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (mnemo_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (index_frequency_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (price_scale_code_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (level_scale_code_value, bytes) =>
                                                          Some ({| symbol_index := symbol_index_value; source_time := source_time_value; instrument_weight := instrument_weight_value; instrument_factor := instrument_factor_value; previous_close := previous_close_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; number_of_conponents := number_of_conponents_value; instrument_id_of_component := instrument_id_of_component_value; mnemo := mnemo_value; index_frequency := index_frequency_value; price_scale_code := price_scale_code_value; level_scale_code := level_scale_code_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexCompositionMessage.

  Module StartRefreshMessage.

    (** A refresh cycle begins with a Start Refresh message on the multicast channels. *)
    Record t := {
      last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_seq_num_value, bytes) =>
          Some ({| last_seq_num := last_seq_num_value |}, bytes)
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

  End StartRefreshMessage.

  Module EndRefreshMessage.

    (** A refresh cycle ends with an End Refresh message on the multicast channels. *)
    Record t := {
      last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_seq_num_value, bytes) =>
          Some ({| last_seq_num := last_seq_num_value |}, bytes)
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

  End EndRefreshMessage.

End QseCashMarketDataV26.
