From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Indices

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

Module WseIndicesV68.

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

  Module RealTimeIndexMessage.

    (** The real time index message handles the real-time characteristics of an index *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      system_id : N;
      index_level : N;
      session_high : N;
      session_low : N;
      ind_index_opening_portfolio : N;
      percent_change_toi : N;
      pct_change_index_val_prev_session : N;
      pct_change_index_val_prev_year : N;
      toi : N;
      point_change : N;
      value_trading : N;
      index_value_bid : N;
      index_value_ask : N;
      mid_spread_index : N;
      difference_central_spread : N;
      num_of_active_instruments : N;
      num_of_instr_of_decreasing_qt : N;
      num_of_instr_of_increasing_qt : N;
      num_of_instr_of_unchanged_qt : N;
      source_time_micro_secs : N;
      level_scale_code : N;
      time_first_high : list byte;
      time_first_low : list byte;
      index_status_indicator : list byte;
      index_level_code : list byte;
      marker_percent_change_toi : list byte;
      marker_pct_chg_index_val_prev_sess : list byte;
      marker_pct_chg_index_val_prev_year : list byte;
      marker_point_change : list byte;
      marker_difference_central_spread : list byte;
      dissemination_frequency_marker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (index_level record < 256 ^ N.of_nat 4)%N /\
      (session_high record < 256 ^ N.of_nat 4)%N /\
      (session_low record < 256 ^ N.of_nat 4)%N /\
      (ind_index_opening_portfolio record < 256 ^ N.of_nat 4)%N /\
      (percent_change_toi record < 256 ^ N.of_nat 4)%N /\
      (pct_change_index_val_prev_session record < 256 ^ N.of_nat 4)%N /\
      (pct_change_index_val_prev_year record < 256 ^ N.of_nat 4)%N /\
      (toi record < 256 ^ N.of_nat 4)%N /\
      (point_change record < 256 ^ N.of_nat 4)%N /\
      (value_trading record < 256 ^ N.of_nat 8)%N /\
      (index_value_bid record < 256 ^ N.of_nat 4)%N /\
      (index_value_ask record < 256 ^ N.of_nat 4)%N /\
      (mid_spread_index record < 256 ^ N.of_nat 4)%N /\
      (difference_central_spread record < 256 ^ N.of_nat 4)%N /\
      (num_of_active_instruments record < 256 ^ N.of_nat 2)%N /\
      (num_of_instr_of_decreasing_qt record < 256 ^ N.of_nat 2)%N /\
      (num_of_instr_of_increasing_qt record < 256 ^ N.of_nat 2)%N /\
      (num_of_instr_of_unchanged_qt record < 256 ^ N.of_nat 2)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (level_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (time_first_high record) = 6 /\
      Datatypes.length (time_first_low record) = 6 /\
      Datatypes.length (index_status_indicator record) = 2 /\
      Datatypes.length (index_level_code record) = 1 /\
      Datatypes.length (marker_percent_change_toi record) = 1 /\
      Datatypes.length (marker_pct_chg_index_val_prev_sess record) = 1 /\
      Datatypes.length (marker_pct_chg_index_val_prev_year record) = 1 /\
      Datatypes.length (marker_point_change record) = 1 /\
      Datatypes.length (marker_difference_central_spread record) = 1 /\
      Datatypes.length (dissemination_frequency_marker record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 4 (index_level record) ++
      encode_uint 4 (session_high record) ++
      encode_uint 4 (session_low record) ++
      encode_uint 4 (ind_index_opening_portfolio record) ++
      encode_uint 4 (percent_change_toi record) ++
      encode_uint 4 (pct_change_index_val_prev_session record) ++
      encode_uint 4 (pct_change_index_val_prev_year record) ++
      encode_uint 4 (toi record) ++
      encode_uint 4 (point_change record) ++
      encode_uint 8 (value_trading record) ++
      encode_uint 4 (index_value_bid record) ++
      encode_uint 4 (index_value_ask record) ++
      encode_uint 4 (mid_spread_index record) ++
      encode_uint 4 (difference_central_spread record) ++
      encode_uint 2 (num_of_active_instruments record) ++
      encode_uint 2 (num_of_instr_of_decreasing_qt record) ++
      encode_uint 2 (num_of_instr_of_increasing_qt record) ++
      encode_uint 2 (num_of_instr_of_unchanged_qt record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (level_scale_code record) ++
      encode_bytes 6 (time_first_high record) ++
      encode_bytes 6 (time_first_low record) ++
      encode_bytes 2 (index_status_indicator record) ++
      encode_bytes 1 (index_level_code record) ++
      encode_bytes 1 (marker_percent_change_toi record) ++
      encode_bytes 1 (marker_pct_chg_index_val_prev_sess record) ++
      encode_bytes 1 (marker_pct_chg_index_val_prev_year record) ++
      encode_bytes 1 (marker_point_change record) ++
      encode_bytes 1 (marker_difference_central_spread record) ++
      encode_bytes 1 (dissemination_frequency_marker record).

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
                  | Some (system_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (index_level_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (session_high_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (session_low_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (ind_index_opening_portfolio_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (percent_change_toi_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (pct_change_index_val_prev_session_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (pct_change_index_val_prev_year_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (toi_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (point_change_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (value_trading_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (index_value_bid_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (index_value_ask_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (mid_spread_index_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (difference_central_spread_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (num_of_active_instruments_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (num_of_instr_of_decreasing_qt_value, bytes) =>
                                                                                      match decode_uint 2 bytes with
                                                                                      | None => None
                                                                                      | Some (num_of_instr_of_increasing_qt_value, bytes) =>
                                                                                          match decode_uint 2 bytes with
                                                                                          | None => None
                                                                                          | Some (num_of_instr_of_unchanged_qt_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (source_time_micro_secs_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (level_scale_code_value, bytes) =>
                                                                                                      match decode_bytes 6 bytes with
                                                                                                      | None => None
                                                                                                      | Some (time_first_high_value, bytes) =>
                                                                                                          match decode_bytes 6 bytes with
                                                                                                          | None => None
                                                                                                          | Some (time_first_low_value, bytes) =>
                                                                                                              match decode_bytes 2 bytes with
                                                                                                              | None => None
                                                                                                              | Some (index_status_indicator_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (index_level_code_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (marker_percent_change_toi_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (marker_pct_chg_index_val_prev_sess_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (marker_pct_chg_index_val_prev_year_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (marker_point_change_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (marker_difference_central_spread_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (dissemination_frequency_marker_value, bytes) =>
                                                                                                                                              Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; system_id := system_id_value; index_level := index_level_value; session_high := session_high_value; session_low := session_low_value; ind_index_opening_portfolio := ind_index_opening_portfolio_value; percent_change_toi := percent_change_toi_value; pct_change_index_val_prev_session := pct_change_index_val_prev_session_value; pct_change_index_val_prev_year := pct_change_index_val_prev_year_value; toi := toi_value; point_change := point_change_value; value_trading := value_trading_value; index_value_bid := index_value_bid_value; index_value_ask := index_value_ask_value; mid_spread_index := mid_spread_index_value; difference_central_spread := difference_central_spread_value; num_of_active_instruments := num_of_active_instruments_value; num_of_instr_of_decreasing_qt := num_of_instr_of_decreasing_qt_value; num_of_instr_of_increasing_qt := num_of_instr_of_increasing_qt_value; num_of_instr_of_unchanged_qt := num_of_instr_of_unchanged_qt_value; source_time_micro_secs := source_time_micro_secs_value; level_scale_code := level_scale_code_value; time_first_high := time_first_high_value; time_first_low := time_first_low_value; index_status_indicator := index_status_indicator_value; index_level_code := index_level_code_value; marker_percent_change_toi := marker_percent_change_toi_value; marker_pct_chg_index_val_prev_sess := marker_pct_chg_index_val_prev_sess_value; marker_pct_chg_index_val_prev_year := marker_pct_chg_index_val_prev_year_value; marker_point_change := marker_point_change_value; marker_difference_central_spread := marker_difference_central_spread_value; dissemination_frequency_marker := dissemination_frequency_marker_value |}, bytes)
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RealTimeIndexMessage.

  Module IndexSummaryMessage.

    (** The index summary message provides a summary of the data calculated in a stock index for a given day *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      system_id : N;
      closing_index_value : N;
      ind_opening_portfolio : N;
      opening_index_value : N;
      session_high : N;
      session_low : N;
      pct_chg_high_index_val_prev_session : N;
      pct_chg_low_index_val_prev_session : N;
      pct_change_index_val_prev_session : N;
      pct_change_index_val_prev_year : N;
      capitalisation_portfolio : N;
      index_adjustment_coefficient : N;
      source_time_micro_secs : N;
      level_scale_code : N;
      capitalisation_scale_code : N;
      index_adjustment_scale_code : N;
      time_closing : list byte;
      time_opening : list byte;
      time_full_opening : list byte;
      time_high : list byte;
      time_low : list byte;
      marker_high : list byte;
      marker_low : list byte;
      marker_closing_prev_session : list byte;
      marker_closing_prev_year : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (closing_index_value record < 256 ^ N.of_nat 4)%N /\
      (ind_opening_portfolio record < 256 ^ N.of_nat 4)%N /\
      (opening_index_value record < 256 ^ N.of_nat 4)%N /\
      (session_high record < 256 ^ N.of_nat 4)%N /\
      (session_low record < 256 ^ N.of_nat 4)%N /\
      (pct_chg_high_index_val_prev_session record < 256 ^ N.of_nat 4)%N /\
      (pct_chg_low_index_val_prev_session record < 256 ^ N.of_nat 4)%N /\
      (pct_change_index_val_prev_session record < 256 ^ N.of_nat 4)%N /\
      (pct_change_index_val_prev_year record < 256 ^ N.of_nat 4)%N /\
      (capitalisation_portfolio record < 256 ^ N.of_nat 4)%N /\
      (index_adjustment_coefficient record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (level_scale_code record < 256 ^ N.of_nat 1)%N /\
      (capitalisation_scale_code record < 256 ^ N.of_nat 1)%N /\
      (index_adjustment_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (time_closing record) = 6 /\
      Datatypes.length (time_opening record) = 6 /\
      Datatypes.length (time_full_opening record) = 6 /\
      Datatypes.length (time_high record) = 6 /\
      Datatypes.length (time_low record) = 6 /\
      Datatypes.length (marker_high record) = 1 /\
      Datatypes.length (marker_low record) = 1 /\
      Datatypes.length (marker_closing_prev_session record) = 1 /\
      Datatypes.length (marker_closing_prev_year record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 4 (closing_index_value record) ++
      encode_uint 4 (ind_opening_portfolio record) ++
      encode_uint 4 (opening_index_value record) ++
      encode_uint 4 (session_high record) ++
      encode_uint 4 (session_low record) ++
      encode_uint 4 (pct_chg_high_index_val_prev_session record) ++
      encode_uint 4 (pct_chg_low_index_val_prev_session record) ++
      encode_uint 4 (pct_change_index_val_prev_session record) ++
      encode_uint 4 (pct_change_index_val_prev_year record) ++
      encode_uint 4 (capitalisation_portfolio record) ++
      encode_uint 4 (index_adjustment_coefficient record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (level_scale_code record) ++
      encode_uint 1 (capitalisation_scale_code record) ++
      encode_uint 1 (index_adjustment_scale_code record) ++
      encode_bytes 6 (time_closing record) ++
      encode_bytes 6 (time_opening record) ++
      encode_bytes 6 (time_full_opening record) ++
      encode_bytes 6 (time_high record) ++
      encode_bytes 6 (time_low record) ++
      encode_bytes 1 (marker_high record) ++
      encode_bytes 1 (marker_low record) ++
      encode_bytes 1 (marker_closing_prev_session record) ++
      encode_bytes 1 (marker_closing_prev_year record) ++
      encode_uint 1 (reserved_1 record).

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
                  | Some (system_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (closing_index_value_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ind_opening_portfolio_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (opening_index_value_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (session_high_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (session_low_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (pct_chg_high_index_val_prev_session_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (pct_chg_low_index_val_prev_session_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (pct_change_index_val_prev_session_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (pct_change_index_val_prev_year_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (capitalisation_portfolio_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (index_adjustment_coefficient_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (source_time_micro_secs_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (level_scale_code_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (capitalisation_scale_code_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (index_adjustment_scale_code_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (time_closing_value, bytes) =>
                                                                                      match decode_bytes 6 bytes with
                                                                                      | None => None
                                                                                      | Some (time_opening_value, bytes) =>
                                                                                          match decode_bytes 6 bytes with
                                                                                          | None => None
                                                                                          | Some (time_full_opening_value, bytes) =>
                                                                                              match decode_bytes 6 bytes with
                                                                                              | None => None
                                                                                              | Some (time_high_value, bytes) =>
                                                                                                  match decode_bytes 6 bytes with
                                                                                                  | None => None
                                                                                                  | Some (time_low_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (marker_high_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (marker_low_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (marker_closing_prev_session_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (marker_closing_prev_year_value, bytes) =>
                                                                                                                      match decode_uint 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (reserved_1_value, bytes) =>
                                                                                                                          Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; system_id := system_id_value; closing_index_value := closing_index_value_value; ind_opening_portfolio := ind_opening_portfolio_value; opening_index_value := opening_index_value_value; session_high := session_high_value; session_low := session_low_value; pct_chg_high_index_val_prev_session := pct_chg_high_index_val_prev_session_value; pct_chg_low_index_val_prev_session := pct_chg_low_index_val_prev_session_value; pct_change_index_val_prev_session := pct_change_index_val_prev_session_value; pct_change_index_val_prev_year := pct_change_index_val_prev_year_value; capitalisation_portfolio := capitalisation_portfolio_value; index_adjustment_coefficient := index_adjustment_coefficient_value; source_time_micro_secs := source_time_micro_secs_value; level_scale_code := level_scale_code_value; capitalisation_scale_code := capitalisation_scale_code_value; index_adjustment_scale_code := index_adjustment_scale_code_value; time_closing := time_closing_value; time_opening := time_opening_value; time_full_opening := time_full_opening_value; time_high := time_high_value; time_low := time_low_value; marker_high := marker_high_value; marker_low := marker_low_value; marker_closing_prev_session := marker_closing_prev_session_value; marker_closing_prev_year := marker_closing_prev_year_value; reserved_1 := reserved_1_value |}, bytes)
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexSummaryMessage.

End WseIndicesV68.
