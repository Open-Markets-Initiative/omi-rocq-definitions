From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Moscow Exchange SIMBA Spectra Futures Instrument Incremental

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
      - a field read in bits
      - a run filling what frames it
      - a block whose stated length holds more than its fields
      - a run counted by a field
      - a field present only on a condition

    License: MIT No Attribution
  *)

Module SpectraFutInfoIncrementalV9120.

  Module IncrementalPacketHeader.

    (** MarketDataDummyMessage *)
    Record t := {
      transact_time : N;
      exchange_trading_session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (exchange_trading_session_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (exchange_trading_session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (exchange_trading_session_id_value, bytes) =>
              Some ({| transact_time := transact_time_value; exchange_trading_session_id := exchange_trading_session_id_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End IncrementalPacketHeader.

  Module SbeHeader.

    (** Root block length, message template id, message schema id and schema version *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 2 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End SbeHeader.

  Module SequenceResetMessage.

    (** SequenceResetMessage *)
    Record t := {
      new_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_seq_no_value, bytes) =>
          Some ({| new_seq_no := new_seq_no_value |}, bytes)
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

  End SequenceResetMessage.

  Module SecurityStatusMessage.

    (** SecurityStatusMessage *)
    Record t := {
      security_id : N;
      symbol : list byte;
      security_trading_status : N;
      high_limit_px : N;
      low_limit_px : N;
      initial_margin_on_buy : N;
      initial_margin_on_sell : N;
      initial_margin_syntetic : N;
      high_limit_px_weekend : N;
      low_limit_px_weekend : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 25 /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (high_limit_px record < 256 ^ N.of_nat 8)%N /\
      (low_limit_px record < 256 ^ N.of_nat 8)%N /\
      (initial_margin_on_buy record < 256 ^ N.of_nat 8)%N /\
      (initial_margin_on_sell record < 256 ^ N.of_nat 8)%N /\
      (initial_margin_syntetic record < 256 ^ N.of_nat 8)%N /\
      (high_limit_px_weekend record < 256 ^ N.of_nat 8)%N /\
      (low_limit_px_weekend record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_id record) ++
      encode_bytes 25 (symbol record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 8 (high_limit_px record) ++
      encode_uint 8 (low_limit_px record) ++
      encode_uint 8 (initial_margin_on_buy record) ++
      encode_uint 8 (initial_margin_on_sell record) ++
      encode_uint 8 (initial_margin_syntetic record) ++
      encode_uint 8 (high_limit_px_weekend record) ++
      encode_uint 8 (low_limit_px_weekend record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_bytes 25 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (security_trading_status_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (high_limit_px_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (low_limit_px_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (initial_margin_on_buy_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (initial_margin_on_sell_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (initial_margin_syntetic_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (high_limit_px_weekend_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (low_limit_px_weekend_value, bytes) =>
                                              Some ({| security_id := security_id_value; symbol := symbol_value; security_trading_status := security_trading_status_value; high_limit_px := high_limit_px_value; low_limit_px := low_limit_px_value; initial_margin_on_buy := initial_margin_on_buy_value; initial_margin_on_sell := initial_margin_on_sell_value; initial_margin_syntetic := initial_margin_syntetic_value; high_limit_px_weekend := high_limit_px_weekend_value; low_limit_px_weekend := low_limit_px_weekend_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
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
      rewrite decode_encode_bytes by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityStatusMessage.

  Module TradingSessionStatusMessage.

    (** TradingSessionStatusMessage *)
    Record t := {
      trad_ses_open_time : N;
      trad_ses_close_time : N;
      trading_session_id : N;
      exchange_trading_session_id_int_32_null_optional : N;
      trad_ses_status : N;
      market_segment_id : list byte;
      trad_ses_event : N;
      trade_period_id : N;
      settl_sess_begin : N;
      clr_sess_begin : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trad_ses_open_time record < 256 ^ N.of_nat 8)%N /\
      (trad_ses_close_time record < 256 ^ N.of_nat 8)%N /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (exchange_trading_session_id_int_32_null_optional record < 256 ^ N.of_nat 4)%N /\
      (trad_ses_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_segment_id record) = 1 /\
      (trad_ses_event record < 256 ^ N.of_nat 1)%N /\
      (trade_period_id record < 256 ^ N.of_nat 8)%N /\
      (settl_sess_begin record < 256 ^ N.of_nat 8)%N /\
      (clr_sess_begin record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trad_ses_open_time record) ++
      encode_uint 8 (trad_ses_close_time record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (exchange_trading_session_id_int_32_null_optional record) ++
      encode_uint 1 (trad_ses_status record) ++
      encode_bytes 1 (market_segment_id record) ++
      encode_uint 1 (trad_ses_event record) ++
      encode_uint 8 (trade_period_id record) ++
      encode_uint 8 (settl_sess_begin record) ++
      encode_uint 8 (clr_sess_begin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trad_ses_open_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trad_ses_close_time_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (exchange_trading_session_id_int_32_null_optional_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trad_ses_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (market_segment_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (trad_ses_event_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_period_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (settl_sess_begin_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (clr_sess_begin_value, bytes) =>
                                              Some ({| trad_ses_open_time := trad_ses_open_time_value; trad_ses_close_time := trad_ses_close_time_value; trading_session_id := trading_session_id_value; exchange_trading_session_id_int_32_null_optional := exchange_trading_session_id_int_32_null_optional_value; trad_ses_status := trad_ses_status_value; market_segment_id := market_segment_id_value; trad_ses_event := trad_ses_event_value; trade_period_id := trade_period_id_value; settl_sess_begin := settl_sess_begin_value; clr_sess_begin := clr_sess_begin_value |}, bytes)
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

  End TradingSessionStatusMessage.

  Module GroupSize.

    (** groupSize *)
    Record t := {
      block_length : N;
      num_in_group_uint_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group_uint_8 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (num_in_group_uint_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_uint_8_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group_uint_8 := num_in_group_uint_8_value |}, bytes)
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

  End GroupSize.

  Module GroupSize2.

    (** groupSize2 *)
    Record t := {
      block_length : N;
      num_in_group_uint_16 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group_uint_16 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 2 (num_in_group_uint_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (num_in_group_uint_16_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group_uint_16 := num_in_group_uint_16_value |}, bytes)
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

  End GroupSize2.

  Module SecurityGroupStatusMessage.

    (** SecurityGroupStatusMessage *)
    Record t := {
      security_group_id : N;
      halt_type : N;
      trade_mode_mask : N;
      group_mask_int_64_null_optional : N;
      section_id_int_32_null_optional : N;
      base_contract_id_int_32_null_optional : N;
      security_trading_status : N;
      status_change_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_group_id record < 256 ^ N.of_nat 8)%N /\
      (halt_type record < 256 ^ N.of_nat 1)%N /\
      (trade_mode_mask record < 256 ^ N.of_nat 4)%N /\
      (group_mask_int_64_null_optional record < 256 ^ N.of_nat 8)%N /\
      (section_id_int_32_null_optional record < 256 ^ N.of_nat 4)%N /\
      (base_contract_id_int_32_null_optional record < 256 ^ N.of_nat 4)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (status_change_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (security_group_id record) ++
      encode_uint 1 (halt_type record) ++
      encode_uint 4 (trade_mode_mask record) ++
      encode_uint 8 (group_mask_int_64_null_optional record) ++
      encode_uint 4 (section_id_int_32_null_optional record) ++
      encode_uint 4 (base_contract_id_int_32_null_optional record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 8 (status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (security_group_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (halt_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_mode_mask_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (group_mask_int_64_null_optional_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (section_id_int_32_null_optional_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (base_contract_id_int_32_null_optional_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (security_trading_status_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (status_change_time_value, bytes) =>
                                      Some ({| security_group_id := security_group_id_value; halt_type := halt_type_value; trade_mode_mask := trade_mode_mask_value; group_mask_int_64_null_optional := group_mask_int_64_null_optional_value; section_id_int_32_null_optional := section_id_int_32_null_optional_value; base_contract_id_int_32_null_optional := base_contract_id_int_32_null_optional_value; security_trading_status := security_trading_status_value; status_change_time := status_change_time_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SecurityGroupStatusMessage.

End SpectraFutInfoIncrementalV9120.
