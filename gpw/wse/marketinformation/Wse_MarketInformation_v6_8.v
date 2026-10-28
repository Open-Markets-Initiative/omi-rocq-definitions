From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Market Information

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
      - the dispatch that chooses a message by its type
  *)

Module WseMarketInformationV68.

  Module PacketHeader.

    (** All messages are preceded by a common packet header format, which section 1.1 states for every Market Information message *)
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

  Module ClassStateChangeMessage.

    (** The Class State Change message indicates a change in the state of a class *)
    Record t := {
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      instrument_group_code : list byte;
      instrument_group_state : list byte;
      session_type : list byte;
      reserved_1 : N;
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
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (class_state record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 3 (instrument_group_code record) ++
      encode_bytes 1 (instrument_group_state record) ++
      encode_bytes 1 (session_type record) ++
      encode_uint 1 (reserved_1 record) ++
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
                                  | Some (reserved_1_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (class_state_value, bytes) =>
                                          Some ({| source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; instrument_group_code := instrument_group_code_value; instrument_group_state := instrument_group_state_value; session_type := session_type_value; reserved_1 := reserved_1_value; class_state := class_state_value |}, bytes)
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

    (** This message supplies a part or a complete electronic message (E-mail), in order to inform members and rebroadcasting members about quotation conditions on a given listed instrument or a set of listed instruments or otherwise about a technical problem *)
    Record t := {
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      scope : list byte;
      title : list byte;
      text_ascii_str_1000 : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (scope record) = 1 /\
      Datatypes.length (title record) = 80 /\
      Datatypes.length (text_ascii_str_1000 record) = 1000 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 1 (scope record) ++
      encode_bytes 80 (title record) ++
      encode_bytes 1000 (text_ascii_str_1000 record) ++
      encode_uint 3 (reserved_3 record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (scope_value, bytes) =>
                          match decode_bytes 80 bytes with
                          | None => None
                          | Some (title_value, bytes) =>
                              match decode_bytes 1000 bytes with
                              | None => None
                              | Some (text_ascii_str_1000_value, bytes) =>
                                  match decode_uint 3 bytes with
                                  | None => None
                                  | Some (reserved_3_value, bytes) =>
                                      Some ({| source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; scope := scope_value; title := title_value; text_ascii_str_1000 := text_ascii_str_1000_value; reserved_3 := reserved_3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1098.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MailMessage.

  Module CollarsMessage.

    (** A Collars message informs Clients of modifications in authorized price fluctuations for an instrument *)
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
      reserved_3 : N;
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
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

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
      encode_uint 3 (reserved_3 record).

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
                                              | Some (reserved_3_value, bytes) =>
                                                  Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; high_collar := high_collar_value; low_collar := low_collar_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; high_scale_code := high_scale_code_value; low_scale_code := low_scale_code_value; collar_type := collar_type_value; reserved_3 := reserved_3_value |}, bytes)
                                              end
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

  Module StartReferentialMessage.

    (** The Start referential message is sent to signal the start of transmission of the Instrument Reference Data Flow *)
    Record t := {
      indicator : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (indicator record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (indicator record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (indicator_value, bytes) =>
          match decode_uint 3 bytes with
          | None => None
          | Some (reserved_3_value, bytes) =>
              Some ({| indicator := indicator_value; reserved_3 := reserved_3_value |}, bytes)
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

    (** The End referential message is sent to signal the end of transmission of the Instrument Reference Data Flow *)
    Record t := {
      indicator : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (indicator record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (indicator record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (indicator_value, bytes) =>
          match decode_uint 3 bytes with
          | None => None
          | Some (reserved_3_value, bytes) =>
              Some ({| indicator := indicator_value; reserved_3 := reserved_3_value |}, bytes)
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

  Module SessionSummaryMessage.

    (** This message contains statistical data *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      date_binary_int_4 : N;
      multiplier : N;
      accumulated_interest : N;
      opening_price : N;
      maximum_price : N;
      minimum_price : N;
      closing_price : N;
      implied_volatility : N;
      average_weighted_price : N;
      reference_price : N;
      pct_change_price : N;
      dividend_rate : N;
      settlement_price : N;
      settlement_value : N;
      reserved_4 : N;
      open_positions : N;
      trading_volume : N;
      transactions_number : N;
      trading_value : N;
      currency_price : N;
      delta : N;
      gamma : N;
      rho : N;
      theta : N;
      vega : N;
      end_trading : N;
      number_of_instruments : N;
      trading_value_currency : N;
      interest_rate : N;
      volatility : N;
      strike_price : N;
      short_selling_trades_number : N;
      volume_short_selling_trades : N;
      value_short_selling_trades : N;
      last_trade_date : N;
      last_trade_price : N;
      block_trades_number : N;
      volume_block_trades : N;
      value_block_trades : N;
      vwap_blocktrade : N;
      maximum_block_price : N;
      minimum_block_price : N;
      system_id : N;
      source_time_micro_secs : N;
      multiplier_scale_code : N;
      accumulated_interest_scale_code : N;
      opening_price_scale_code : N;
      maximum_price_scale_code : N;
      minimum_price_scale_code : N;
      closing_price_scale_code : N;
      implied_volatility_scale_code : N;
      average_weighted_price_scale_code : N;
      reference_price_scale_code : N;
      pct_change_price_scale_code : N;
      dividend_rate_scale_code : N;
      settlement_price_scale_code : N;
      settlement_value_scale_code : N;
      reserved_1 : N;
      trading_value_scale_code : N;
      currency_price_scale_code : N;
      delta_scale_code : N;
      gamma_scale_code : N;
      rho_scale_code : N;
      theta_scale_code : N;
      vega_scale_code : N;
      trading_value_currency_scale_code : N;
      interest_rate_scale_code : N;
      volatility_scale_code : N;
      strike_price_scale_code : N;
      value_short_selling_trades_scale_code : N;
      last_trade_price_scale_code : N;
      value_block_trades_scale_code : N;
      vwap_blocktrade_scale_code : N;
      maximum_block_price_scale_code : N;
      minimum_block_price_scale_code : N;
      status_indicator : list byte;
      sector : list byte;
      market : list byte;
      second_reserved_1 : N;
      short_sale : list byte;
      marker_pct_change_price : list byte;
      symbol_delta : list byte;
      symbol_gamma : list byte;
      symbol_rho : list byte;
      symbol_theta : list byte;
      symbol_vega : list byte;
      third_reserved_1 : N;
      fourth_reserved_1 : N;
      fifth_reserved_1 : N;
      sixth_reserved_1 : N;
      seventh_reserved_1 : N;
      eighth_reserved_1 : N;
      segment : list byte;
      lower_liquidity : list byte;
      dividend : list byte;
      subscription_right : list byte;
      split : list byte;
      interim_dividend_right : list byte;
      quotation_system : list byte;
      liquidity_support_pge : list byte;
      ninth_reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (date_binary_int_4 record < 256 ^ N.of_nat 4)%N /\
      (multiplier record < 256 ^ N.of_nat 4)%N /\
      (accumulated_interest record < 256 ^ N.of_nat 4)%N /\
      (opening_price record < 256 ^ N.of_nat 4)%N /\
      (maximum_price record < 256 ^ N.of_nat 4)%N /\
      (minimum_price record < 256 ^ N.of_nat 4)%N /\
      (closing_price record < 256 ^ N.of_nat 4)%N /\
      (implied_volatility record < 256 ^ N.of_nat 4)%N /\
      (average_weighted_price record < 256 ^ N.of_nat 4)%N /\
      (reference_price record < 256 ^ N.of_nat 4)%N /\
      (pct_change_price record < 256 ^ N.of_nat 4)%N /\
      (dividend_rate record < 256 ^ N.of_nat 4)%N /\
      (settlement_price record < 256 ^ N.of_nat 4)%N /\
      (settlement_value record < 256 ^ N.of_nat 4)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      (open_positions record < 256 ^ N.of_nat 4)%N /\
      (trading_volume record < 256 ^ N.of_nat 4)%N /\
      (transactions_number record < 256 ^ N.of_nat 4)%N /\
      (trading_value record < 256 ^ N.of_nat 8)%N /\
      (currency_price record < 256 ^ N.of_nat 4)%N /\
      (delta record < 256 ^ N.of_nat 4)%N /\
      (gamma record < 256 ^ N.of_nat 4)%N /\
      (rho record < 256 ^ N.of_nat 4)%N /\
      (theta record < 256 ^ N.of_nat 4)%N /\
      (vega record < 256 ^ N.of_nat 4)%N /\
      (end_trading record < 256 ^ N.of_nat 4)%N /\
      (number_of_instruments record < 256 ^ N.of_nat 4)%N /\
      (trading_value_currency record < 256 ^ N.of_nat 8)%N /\
      (interest_rate record < 256 ^ N.of_nat 4)%N /\
      (volatility record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (short_selling_trades_number record < 256 ^ N.of_nat 4)%N /\
      (volume_short_selling_trades record < 256 ^ N.of_nat 4)%N /\
      (value_short_selling_trades record < 256 ^ N.of_nat 4)%N /\
      (last_trade_date record < 256 ^ N.of_nat 4)%N /\
      (last_trade_price record < 256 ^ N.of_nat 4)%N /\
      (block_trades_number record < 256 ^ N.of_nat 4)%N /\
      (volume_block_trades record < 256 ^ N.of_nat 4)%N /\
      (value_block_trades record < 256 ^ N.of_nat 4)%N /\
      (vwap_blocktrade record < 256 ^ N.of_nat 4)%N /\
      (maximum_block_price record < 256 ^ N.of_nat 4)%N /\
      (minimum_block_price record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (multiplier_scale_code record < 256 ^ N.of_nat 1)%N /\
      (accumulated_interest_scale_code record < 256 ^ N.of_nat 1)%N /\
      (opening_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (maximum_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (minimum_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (closing_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (implied_volatility_scale_code record < 256 ^ N.of_nat 1)%N /\
      (average_weighted_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (reference_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (pct_change_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (dividend_rate_scale_code record < 256 ^ N.of_nat 1)%N /\
      (settlement_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (settlement_value_scale_code record < 256 ^ N.of_nat 1)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (trading_value_scale_code record < 256 ^ N.of_nat 1)%N /\
      (currency_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (delta_scale_code record < 256 ^ N.of_nat 1)%N /\
      (gamma_scale_code record < 256 ^ N.of_nat 1)%N /\
      (rho_scale_code record < 256 ^ N.of_nat 1)%N /\
      (theta_scale_code record < 256 ^ N.of_nat 1)%N /\
      (vega_scale_code record < 256 ^ N.of_nat 1)%N /\
      (trading_value_currency_scale_code record < 256 ^ N.of_nat 1)%N /\
      (interest_rate_scale_code record < 256 ^ N.of_nat 1)%N /\
      (volatility_scale_code record < 256 ^ N.of_nat 1)%N /\
      (strike_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (value_short_selling_trades_scale_code record < 256 ^ N.of_nat 1)%N /\
      (last_trade_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (value_block_trades_scale_code record < 256 ^ N.of_nat 1)%N /\
      (vwap_blocktrade_scale_code record < 256 ^ N.of_nat 1)%N /\
      (maximum_block_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (minimum_block_price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (status_indicator record) = 1 /\
      Datatypes.length (sector record) = 3 /\
      Datatypes.length (market record) = 1 /\
      (second_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (short_sale record) = 1 /\
      Datatypes.length (marker_pct_change_price record) = 1 /\
      Datatypes.length (symbol_delta record) = 1 /\
      Datatypes.length (symbol_gamma record) = 1 /\
      Datatypes.length (symbol_rho record) = 1 /\
      Datatypes.length (symbol_theta record) = 1 /\
      Datatypes.length (symbol_vega record) = 1 /\
      (third_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (fourth_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (fifth_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (sixth_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (seventh_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (eighth_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (segment record) = 2 /\
      Datatypes.length (lower_liquidity record) = 1 /\
      Datatypes.length (dividend record) = 2 /\
      Datatypes.length (subscription_right record) = 2 /\
      Datatypes.length (split record) = 2 /\
      Datatypes.length (interim_dividend_right record) = 2 /\
      Datatypes.length (quotation_system record) = 2 /\
      Datatypes.length (liquidity_support_pge record) = 2 /\
      (ninth_reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (date_binary_int_4 record) ++
      encode_uint 4 (multiplier record) ++
      encode_uint 4 (accumulated_interest record) ++
      encode_uint 4 (opening_price record) ++
      encode_uint 4 (maximum_price record) ++
      encode_uint 4 (minimum_price record) ++
      encode_uint 4 (closing_price record) ++
      encode_uint 4 (implied_volatility record) ++
      encode_uint 4 (average_weighted_price record) ++
      encode_uint 4 (reference_price record) ++
      encode_uint 4 (pct_change_price record) ++
      encode_uint 4 (dividend_rate record) ++
      encode_uint 4 (settlement_price record) ++
      encode_uint 4 (settlement_value record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_uint 4 (open_positions record) ++
      encode_uint 4 (trading_volume record) ++
      encode_uint 4 (transactions_number record) ++
      encode_uint 8 (trading_value record) ++
      encode_uint 4 (currency_price record) ++
      encode_uint 4 (delta record) ++
      encode_uint 4 (gamma record) ++
      encode_uint 4 (rho record) ++
      encode_uint 4 (theta record) ++
      encode_uint 4 (vega record) ++
      encode_uint 4 (end_trading record) ++
      encode_uint 4 (number_of_instruments record) ++
      encode_uint 8 (trading_value_currency record) ++
      encode_uint 4 (interest_rate record) ++
      encode_uint 4 (volatility record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (short_selling_trades_number record) ++
      encode_uint 4 (volume_short_selling_trades record) ++
      encode_uint 4 (value_short_selling_trades record) ++
      encode_uint 4 (last_trade_date record) ++
      encode_uint 4 (last_trade_price record) ++
      encode_uint 4 (block_trades_number record) ++
      encode_uint 4 (volume_block_trades record) ++
      encode_uint 4 (value_block_trades record) ++
      encode_uint 4 (vwap_blocktrade record) ++
      encode_uint 4 (maximum_block_price record) ++
      encode_uint 4 (minimum_block_price record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (multiplier_scale_code record) ++
      encode_uint 1 (accumulated_interest_scale_code record) ++
      encode_uint 1 (opening_price_scale_code record) ++
      encode_uint 1 (maximum_price_scale_code record) ++
      encode_uint 1 (minimum_price_scale_code record) ++
      encode_uint 1 (closing_price_scale_code record) ++
      encode_uint 1 (implied_volatility_scale_code record) ++
      encode_uint 1 (average_weighted_price_scale_code record) ++
      encode_uint 1 (reference_price_scale_code record) ++
      encode_uint 1 (pct_change_price_scale_code record) ++
      encode_uint 1 (dividend_rate_scale_code record) ++
      encode_uint 1 (settlement_price_scale_code record) ++
      encode_uint 1 (settlement_value_scale_code record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 1 (trading_value_scale_code record) ++
      encode_uint 1 (currency_price_scale_code record) ++
      encode_uint 1 (delta_scale_code record) ++
      encode_uint 1 (gamma_scale_code record) ++
      encode_uint 1 (rho_scale_code record) ++
      encode_uint 1 (theta_scale_code record) ++
      encode_uint 1 (vega_scale_code record) ++
      encode_uint 1 (trading_value_currency_scale_code record) ++
      encode_uint 1 (interest_rate_scale_code record) ++
      encode_uint 1 (volatility_scale_code record) ++
      encode_uint 1 (strike_price_scale_code record) ++
      encode_uint 1 (value_short_selling_trades_scale_code record) ++
      encode_uint 1 (last_trade_price_scale_code record) ++
      encode_uint 1 (value_block_trades_scale_code record) ++
      encode_uint 1 (vwap_blocktrade_scale_code record) ++
      encode_uint 1 (maximum_block_price_scale_code record) ++
      encode_uint 1 (minimum_block_price_scale_code record) ++
      encode_bytes 1 (status_indicator record) ++
      encode_bytes 3 (sector record) ++
      encode_bytes 1 (market record) ++
      encode_uint 1 (second_reserved_1 record) ++
      encode_bytes 1 (short_sale record) ++
      encode_bytes 1 (marker_pct_change_price record) ++
      encode_bytes 1 (symbol_delta record) ++
      encode_bytes 1 (symbol_gamma record) ++
      encode_bytes 1 (symbol_rho record) ++
      encode_bytes 1 (symbol_theta record) ++
      encode_bytes 1 (symbol_vega record) ++
      encode_uint 1 (third_reserved_1 record) ++
      encode_uint 1 (fourth_reserved_1 record) ++
      encode_uint 1 (fifth_reserved_1 record) ++
      encode_uint 1 (sixth_reserved_1 record) ++
      encode_uint 1 (seventh_reserved_1 record) ++
      encode_uint 1 (eighth_reserved_1 record) ++
      encode_bytes 2 (segment record) ++
      encode_bytes 1 (lower_liquidity record) ++
      encode_bytes 2 (dividend record) ++
      encode_bytes 2 (subscription_right record) ++
      encode_bytes 2 (split record) ++
      encode_bytes 2 (interim_dividend_right record) ++
      encode_bytes 2 (quotation_system record) ++
      encode_bytes 2 (liquidity_support_pge record) ++
      encode_uint 1 (ninth_reserved_1 record).

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
                  | Some (date_binary_int_4_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (multiplier_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (accumulated_interest_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (opening_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (maximum_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (minimum_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (closing_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (implied_volatility_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (average_weighted_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (reference_price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (pct_change_price_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (dividend_rate_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (settlement_price_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (settlement_value_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (reserved_4_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (open_positions_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (trading_volume_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (transactions_number_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (trading_value_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (currency_price_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (delta_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (gamma_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (rho_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (theta_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (vega_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (end_trading_value, bytes) =>
                                                                                                                          match decode_uint 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (number_of_instruments_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (trading_value_currency_value, bytes) =>
                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (interest_rate_value, bytes) =>
                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (volatility_value, bytes) =>
                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (strike_price_value, bytes) =>
                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (short_selling_trades_number_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (volume_short_selling_trades_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (value_short_selling_trades_value, bytes) =>
                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (last_trade_date_value, bytes) =>
                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (last_trade_price_value, bytes) =>
                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (block_trades_number_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (volume_block_trades_value, bytes) =>
                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (value_block_trades_value, bytes) =>
                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (vwap_blocktrade_value, bytes) =>
                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (maximum_block_price_value, bytes) =>
                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (minimum_block_price_value, bytes) =>
                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (system_id_value, bytes) =>
                                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (source_time_micro_secs_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (multiplier_scale_code_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (accumulated_interest_scale_code_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (opening_price_scale_code_value, bytes) =>
                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (maximum_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (minimum_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (closing_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (implied_volatility_scale_code_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (average_weighted_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (reference_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (pct_change_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (dividend_rate_scale_code_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (settlement_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (settlement_value_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (trading_value_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (currency_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (delta_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (gamma_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (rho_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (theta_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (vega_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (trading_value_currency_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (interest_rate_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (volatility_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (strike_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (value_short_selling_trades_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (last_trade_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (value_block_trades_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (vwap_blocktrade_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (maximum_block_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (minimum_block_price_scale_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (status_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (sector_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (market_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (second_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (short_sale_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (marker_pct_change_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (symbol_delta_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (symbol_gamma_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (symbol_rho_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (symbol_theta_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (symbol_vega_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (third_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (fourth_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                  | Some (fifth_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                      | Some (sixth_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                          | Some (seventh_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                              | Some (eighth_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (segment_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                      | Some (lower_liquidity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                          | Some (dividend_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                              | Some (subscription_right_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (split_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (interim_dividend_right_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (quotation_system_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (liquidity_support_pge_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (ninth_reserved_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                      Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; date_binary_int_4 := date_binary_int_4_value; multiplier := multiplier_value; accumulated_interest := accumulated_interest_value; opening_price := opening_price_value; maximum_price := maximum_price_value; minimum_price := minimum_price_value; closing_price := closing_price_value; implied_volatility := implied_volatility_value; average_weighted_price := average_weighted_price_value; reference_price := reference_price_value; pct_change_price := pct_change_price_value; dividend_rate := dividend_rate_value; settlement_price := settlement_price_value; settlement_value := settlement_value_value; reserved_4 := reserved_4_value; open_positions := open_positions_value; trading_volume := trading_volume_value; transactions_number := transactions_number_value; trading_value := trading_value_value; currency_price := currency_price_value; delta := delta_value; gamma := gamma_value; rho := rho_value; theta := theta_value; vega := vega_value; end_trading := end_trading_value; number_of_instruments := number_of_instruments_value; trading_value_currency := trading_value_currency_value; interest_rate := interest_rate_value; volatility := volatility_value; strike_price := strike_price_value; short_selling_trades_number := short_selling_trades_number_value; volume_short_selling_trades := volume_short_selling_trades_value; value_short_selling_trades := value_short_selling_trades_value; last_trade_date := last_trade_date_value; last_trade_price := last_trade_price_value; block_trades_number := block_trades_number_value; volume_block_trades := volume_block_trades_value; value_block_trades := value_block_trades_value; vwap_blocktrade := vwap_blocktrade_value; maximum_block_price := maximum_block_price_value; minimum_block_price := minimum_block_price_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; multiplier_scale_code := multiplier_scale_code_value; accumulated_interest_scale_code := accumulated_interest_scale_code_value; opening_price_scale_code := opening_price_scale_code_value; maximum_price_scale_code := maximum_price_scale_code_value; minimum_price_scale_code := minimum_price_scale_code_value; closing_price_scale_code := closing_price_scale_code_value; implied_volatility_scale_code := implied_volatility_scale_code_value; average_weighted_price_scale_code := average_weighted_price_scale_code_value; reference_price_scale_code := reference_price_scale_code_value; pct_change_price_scale_code := pct_change_price_scale_code_value; dividend_rate_scale_code := dividend_rate_scale_code_value; settlement_price_scale_code := settlement_price_scale_code_value; settlement_value_scale_code := settlement_value_scale_code_value; reserved_1 := reserved_1_value; trading_value_scale_code := trading_value_scale_code_value; currency_price_scale_code := currency_price_scale_code_value; delta_scale_code := delta_scale_code_value; gamma_scale_code := gamma_scale_code_value; rho_scale_code := rho_scale_code_value; theta_scale_code := theta_scale_code_value; vega_scale_code := vega_scale_code_value; trading_value_currency_scale_code := trading_value_currency_scale_code_value; interest_rate_scale_code := interest_rate_scale_code_value; volatility_scale_code := volatility_scale_code_value; strike_price_scale_code := strike_price_scale_code_value; value_short_selling_trades_scale_code := value_short_selling_trades_scale_code_value; last_trade_price_scale_code := last_trade_price_scale_code_value; value_block_trades_scale_code := value_block_trades_scale_code_value; vwap_blocktrade_scale_code := vwap_blocktrade_scale_code_value; maximum_block_price_scale_code := maximum_block_price_scale_code_value; minimum_block_price_scale_code := minimum_block_price_scale_code_value; status_indicator := status_indicator_value; sector := sector_value; market := market_value; second_reserved_1 := second_reserved_1_value; short_sale := short_sale_value; marker_pct_change_price := marker_pct_change_price_value; symbol_delta := symbol_delta_value; symbol_gamma := symbol_gamma_value; symbol_rho := symbol_rho_value; symbol_theta := symbol_theta_value; symbol_vega := symbol_vega_value; third_reserved_1 := third_reserved_1_value; fourth_reserved_1 := fourth_reserved_1_value; fifth_reserved_1 := fifth_reserved_1_value; sixth_reserved_1 := sixth_reserved_1_value; seventh_reserved_1 := seventh_reserved_1_value; eighth_reserved_1 := eighth_reserved_1_value; segment := segment_value; lower_liquidity := lower_liquidity_value; dividend := dividend_value; subscription_right := subscription_right_value; split := split_value; interim_dividend_right := interim_dividend_right_value; quotation_system := quotation_system_value; liquidity_support_pge := liquidity_support_pge_value; ninth_reserved_1 := ninth_reserved_1_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 260.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 [bound_95 [bound_96 [bound_97 [bound_98 [bound_99 [bound_100 [bound_101 [bound_102 bound_103]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_uint by exact bound_50.
      rewrite decode_encode_uint by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_uint by exact bound_60.
      rewrite decode_encode_uint by exact bound_61.
      rewrite decode_encode_uint by exact bound_62.
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
      rewrite decode_encode_uint by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_uint by exact bound_76.
      rewrite decode_encode_uint by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_bytes by exact bound_80.
      rewrite decode_encode_uint by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_bytes by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_bytes by exact bound_85.
      rewrite decode_encode_bytes by exact bound_86.
      rewrite decode_encode_bytes by exact bound_87.
      rewrite decode_encode_bytes by exact bound_88.
      rewrite decode_encode_uint by exact bound_89.
      rewrite decode_encode_uint by exact bound_90.
      rewrite decode_encode_uint by exact bound_91.
      rewrite decode_encode_uint by exact bound_92.
      rewrite decode_encode_uint by exact bound_93.
      rewrite decode_encode_uint by exact bound_94.
      rewrite decode_encode_bytes by exact bound_95.
      rewrite decode_encode_bytes by exact bound_96.
      rewrite decode_encode_bytes by exact bound_97.
      rewrite decode_encode_bytes by exact bound_98.
      rewrite decode_encode_bytes by exact bound_99.
      rewrite decode_encode_bytes by exact bound_100.
      rewrite decode_encode_bytes by exact bound_101.
      rewrite decode_encode_bytes by exact bound_102.
      rewrite decode_encode_uint by exact bound_103.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SessionSummaryMessage.

  Module InstrumentStateChangeMessage.

    (** An 'Instrument State Change' message is generated by the trading engines to announce a change in the state of an instrument *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      reserved_2 : N;
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
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
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
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (reserved_2 record) ++
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
      encode_uint 1 (reserved_1 record).

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
                          | Some (reserved_2_value, bytes) =>
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
                                                                      | Some (reserved_1_value, bytes) =>
                                                                          Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; reserved_2 := reserved_2_value; start_date_halting := start_date_halting_value; start_time_halting := start_time_halting_value; prog_opening_time := prog_opening_time_value; order_entry_rejection := order_entry_rejection_value; instrument_state := instrument_state_value; instrument_trading_status := instrument_trading_status_value; halt_reason := halt_reason_value; action_affecting_state := action_affecting_state_value; instrument_state_tcs := instrument_state_tcs_value; period_side := period_side_value; reserved_1 := reserved_1_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

  End InstrumentStateChangeMessage.

  Module IndicativeMatchingPriceMessage.

    (** The Indicative matching price message indicates an instrument's theoretical opening price (also known as an indicative opening price):  An IMP-message is sent if the indicative matching price or – volume varies *)
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

  Module ShortSaleChangeMessage.

    (** The Short Sale Change message indicates whether an instrument short sale is suspended or re-authorized *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      system_id : N;
      source_time_micro_secs : N;
      text_ascii_ch_100 : list byte;
      authority : list byte;
      ss_market_maker : list byte;
      ss_non_market_maker : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (text_ascii_ch_100 record) = 100 /\
      Datatypes.length (authority record) = 1 /\
      Datatypes.length (ss_market_maker record) = 1 /\
      Datatypes.length (ss_non_market_maker record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 100 (text_ascii_ch_100 record) ++
      encode_bytes 1 (authority record) ++
      encode_bytes 1 (ss_market_maker record) ++
      encode_bytes 1 (ss_non_market_maker record) ++
      encode_uint 3 (reserved_3 record).

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
                          match decode_bytes 100 bytes with
                          | None => None
                          | Some (text_ascii_ch_100_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (authority_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (ss_market_maker_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (ss_non_market_maker_value, bytes) =>
                                          match decode_uint 3 bytes with
                                          | None => None
                                          | Some (reserved_3_value, bytes) =>
                                              Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; text_ascii_ch_100 := text_ascii_ch_100_value; authority := authority_value; ss_market_maker := ss_market_maker_value; ss_non_market_maker := ss_non_market_maker_value; reserved_3 := reserved_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 124.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortSaleChangeMessage.

  Module TreasuryBondFuturesData.

    (** Body Message for InternalMsgType = 02, which informs about the structure of the basket of treasury bonds for a given bond future for the next trading day *)
    Record t := {
      isin_code : list byte;
      date_of_first_quotation : list byte;
      short_name : list byte;
      date_ascii_str_8 : list byte;
      underlying_isin_code : list byte;
      treasury_bond_1_isin_code : list byte;
      conversion_coefficient_factor_1 : list byte;
      treasury_bond_2_isin_code : list byte;
      conversion_coefficient_factor_2 : list byte;
      treasury_bond_3_isin_code : list byte;
      conversion_coefficient_factor_3 : list byte;
      treasury_bond_4_isin_code : list byte;
      conversion_coefficient_factor_4 : list byte;
      treasury_bond_5_isin_code : list byte;
      conversion_coefficient_factor_5 : list byte;
      reserved_59 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (date_of_first_quotation record) = 8 /\
      Datatypes.length (short_name record) = 16 /\
      Datatypes.length (date_ascii_str_8 record) = 8 /\
      Datatypes.length (underlying_isin_code record) = 12 /\
      Datatypes.length (treasury_bond_1_isin_code record) = 12 /\
      Datatypes.length (conversion_coefficient_factor_1 record) = 9 /\
      Datatypes.length (treasury_bond_2_isin_code record) = 12 /\
      Datatypes.length (conversion_coefficient_factor_2 record) = 9 /\
      Datatypes.length (treasury_bond_3_isin_code record) = 12 /\
      Datatypes.length (conversion_coefficient_factor_3 record) = 9 /\
      Datatypes.length (treasury_bond_4_isin_code record) = 12 /\
      Datatypes.length (conversion_coefficient_factor_4 record) = 9 /\
      Datatypes.length (treasury_bond_5_isin_code record) = 12 /\
      Datatypes.length (conversion_coefficient_factor_5 record) = 9 /\
      Datatypes.length (reserved_59 record) = 59.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (date_of_first_quotation record) ++
      encode_bytes 16 (short_name record) ++
      encode_bytes 8 (date_ascii_str_8 record) ++
      encode_bytes 12 (underlying_isin_code record) ++
      encode_bytes 12 (treasury_bond_1_isin_code record) ++
      encode_bytes 9 (conversion_coefficient_factor_1 record) ++
      encode_bytes 12 (treasury_bond_2_isin_code record) ++
      encode_bytes 9 (conversion_coefficient_factor_2 record) ++
      encode_bytes 12 (treasury_bond_3_isin_code record) ++
      encode_bytes 9 (conversion_coefficient_factor_3 record) ++
      encode_bytes 12 (treasury_bond_4_isin_code record) ++
      encode_bytes 9 (conversion_coefficient_factor_4 record) ++
      encode_bytes 12 (treasury_bond_5_isin_code record) ++
      encode_bytes 9 (conversion_coefficient_factor_5 record) ++
      encode_bytes 59 (reserved_59 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (date_of_first_quotation_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (short_name_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (date_ascii_str_8_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (underlying_isin_code_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (treasury_bond_1_isin_code_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (conversion_coefficient_factor_1_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (treasury_bond_2_isin_code_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (conversion_coefficient_factor_2_value, bytes) =>
                                          match decode_bytes 12 bytes with
                                          | None => None
                                          | Some (treasury_bond_3_isin_code_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (conversion_coefficient_factor_3_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (treasury_bond_4_isin_code_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (conversion_coefficient_factor_4_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (treasury_bond_5_isin_code_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (conversion_coefficient_factor_5_value, bytes) =>
                                                                  match decode_bytes 59 bytes with
                                                                  | None => None
                                                                  | Some (reserved_59_value, bytes) =>
                                                                      Some ({| isin_code := isin_code_value; date_of_first_quotation := date_of_first_quotation_value; short_name := short_name_value; date_ascii_str_8 := date_ascii_str_8_value; underlying_isin_code := underlying_isin_code_value; treasury_bond_1_isin_code := treasury_bond_1_isin_code_value; conversion_coefficient_factor_1 := conversion_coefficient_factor_1_value; treasury_bond_2_isin_code := treasury_bond_2_isin_code_value; conversion_coefficient_factor_2 := conversion_coefficient_factor_2_value; treasury_bond_3_isin_code := treasury_bond_3_isin_code_value; conversion_coefficient_factor_3 := conversion_coefficient_factor_3_value; treasury_bond_4_isin_code := treasury_bond_4_isin_code_value; conversion_coefficient_factor_4 := conversion_coefficient_factor_4_value; treasury_bond_5_isin_code := treasury_bond_5_isin_code_value; conversion_coefficient_factor_5 := conversion_coefficient_factor_5_value; reserved_59 := reserved_59_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 220.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TreasuryBondFuturesData.

  Module Kid.

    (** Body Message for InternalMsgType field = 03, which informs about the selected values for PRIIPs key information for the given trading day and includes the link to the issuer's website *)
    Record t := {
      isin_code : list byte;
      type_of_instrument_ascii_str_4 : list byte;
      kid_version : list byte;
      kid_issue_date : list byte;
      value_at_risk : list byte;
      holding_period : list byte;
      priip_kid_url : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (type_of_instrument_ascii_str_4 record) = 4 /\
      Datatypes.length (kid_version record) = 10 /\
      Datatypes.length (kid_issue_date record) = 8 /\
      Datatypes.length (value_at_risk record) = 1 /\
      Datatypes.length (holding_period record) = 3 /\
      Datatypes.length (priip_kid_url record) = 182.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 4 (type_of_instrument_ascii_str_4 record) ++
      encode_bytes 10 (kid_version record) ++
      encode_bytes 8 (kid_issue_date record) ++
      encode_bytes 1 (value_at_risk record) ++
      encode_bytes 3 (holding_period record) ++
      encode_bytes 182 (priip_kid_url record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (type_of_instrument_ascii_str_4_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (kid_version_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (kid_issue_date_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (value_at_risk_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (holding_period_value, bytes) =>
                              match decode_bytes 182 bytes with
                              | None => None
                              | Some (priip_kid_url_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; type_of_instrument_ascii_str_4 := type_of_instrument_ascii_str_4_value; kid_version := kid_version_value; kid_issue_date := kid_issue_date_value; value_at_risk := value_at_risk_value; holding_period := holding_period_value; priip_kid_url := priip_kid_url_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 220.
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

  End Kid.

  Module MarketConditions.

    (** Body Message for InternalMsgType field = 04, 05, which informs about the beginning or the end of a Stressed or an Exceptional Market Conditions State for a given instrument *)
    Record t := {
      isin_code : list byte;
      market_conditions_state : list byte;
      market_conditions_number : list byte;
      reserved_203 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (market_conditions_state record) = 1 /\
      Datatypes.length (market_conditions_number record) = 4 /\
      Datatypes.length (reserved_203 record) = 203.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 1 (market_conditions_state record) ++
      encode_bytes 4 (market_conditions_number record) ++
      encode_bytes 203 (reserved_203 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_conditions_state_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_conditions_number_value, bytes) =>
                  match decode_bytes 203 bytes with
                  | None => None
                  | Some (reserved_203_value, bytes) =>
                      Some ({| isin_code := isin_code_value; market_conditions_state := market_conditions_state_value; market_conditions_number := market_conditions_number_value; reserved_203 := reserved_203_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 220.
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

  End MarketConditions.

  Module OpenPositionMessage.

    (** The Open Position message indicates the current number of open positions for a particular instrument *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      trading_date : list byte;
      open_position : N;
      transaction_number : N;
      system_id : N;
      source_time_micro_secs : N;
      open_position_indicator : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_date record) = 8 /\
      (open_position record < 256 ^ N.of_nat 4)%N /\
      (transaction_number record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (open_position_indicator record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_bytes 8 (trading_date record) ++
      encode_uint 4 (open_position record) ++
      encode_uint 4 (transaction_number record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 1 (open_position_indicator record) ++
      encode_uint 1 (reserved_1 record).

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
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trading_date_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (open_position_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (transaction_number_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (system_id_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (source_time_micro_secs_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (open_position_indicator_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (reserved_1_value, bytes) =>
                                              Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; trading_date := trading_date_value; open_position := open_position_value; transaction_number := transaction_number_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; open_position_indicator := open_position_indicator_value; reserved_1 := reserved_1_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpenPositionMessage.

End WseMarketInformationV68.
