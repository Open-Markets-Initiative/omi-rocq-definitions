From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Euronext Market Data Gateway

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
      - a Conversion rule
      - a block whose stated length holds more than its fields
      - a run counted by a field
      - a Empty element

    License: MIT No Attribution
  *)

Module EuronextOptiqMarketDataGatewayV524.

  Module MessageHeader.

    (** Optiq Sbe message header — message identifiers and length of message root *)
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
      encode_uint_le 2 (block_length record) ++
      encode_uint_le 2 (template_id record) ++
      encode_uint_le 2 (schema_id record) ++
      encode_uint_le 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint_le 2 bytes with
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
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module StartOfDayMessage.

    (** StartOfDayMessage *)
    Record t := {
      md_seq_num : N;
      session_trading_day : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (session_trading_day record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num record) ++
      encode_uint_le 2 (session_trading_day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (session_trading_day_value, bytes) =>
              Some ({| md_seq_num := md_seq_num_value; session_trading_day := session_trading_day_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StartOfDayMessage.

  Module EndOfDayMessage.

    (** EndOfDayMessage *)
    Record t := {
      md_seq_num : N;
      session_trading_day : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (session_trading_day record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num record) ++
      encode_uint_le 2 (session_trading_day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (session_trading_day_value, bytes) =>
              Some ({| md_seq_num := md_seq_num_value; session_trading_day := session_trading_day_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EndOfDayMessage.

  Module HealthStatusMessage.

    (** HealthStatusMessage *)
    Record t := {
      md_seq_num : N;
      event_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (event_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num record) ++
      encode_uint_le 8 (event_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (event_time_value, bytes) =>
              Some ({| md_seq_num := md_seq_num_value; event_time := event_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End HealthStatusMessage.

  Module TechnicalNotificationMessage.

    (** TechnicalNotificationMessage *)
    Record t := {
      md_seq_num_optional : N;
      technical_notification_type : N;
      rebroadcast_indicator : N;
      retransmission_start_time : N;
      retransmission_end_time : N;
      symbol_index_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num_optional record < 256 ^ N.of_nat 8)%N /\
      (technical_notification_type record < 256 ^ N.of_nat 1)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      (retransmission_start_time record < 256 ^ N.of_nat 8)%N /\
      (retransmission_end_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_index_optional record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num_optional record) ++
      encode_uint 1 (technical_notification_type record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_uint_le 8 (retransmission_start_time record) ++
      encode_uint_le 8 (retransmission_end_time record) ++
      encode_uint_le 4 (symbol_index_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_optional_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (technical_notification_type_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (rebroadcast_indicator_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (retransmission_start_time_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (retransmission_end_time_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (symbol_index_optional_value, bytes) =>
                              Some ({| md_seq_num_optional := md_seq_num_optional_value; technical_notification_type := technical_notification_type_value; rebroadcast_indicator := rebroadcast_indicator_value; retransmission_start_time := retransmission_start_time_value; retransmission_end_time := retransmission_end_time_value; symbol_index_optional := symbol_index_optional_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TechnicalNotificationMessage.

  Module GroupSizeEncoding.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End GroupSizeEncoding.

  Module RealTimeIndexMessage.

    (** RealTimeIndexMessage *)
    Record t := {
      md_seq_num : N;
      rebroadcast_indicator : N;
      emm : N;
      event_time : N;
      symbol_index : N;
      index_level : N;
      pctg_of_capitalization : N;
      prct_varfrom_prev_close : N;
      num_traded_instruments : N;
      index_level_type : N;
      index_price_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (event_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (index_level record < 256 ^ N.of_nat 8)%N /\
      (pctg_of_capitalization record < 256 ^ N.of_nat 8)%N /\
      (prct_varfrom_prev_close record < 256 ^ N.of_nat 8)%N /\
      (num_traded_instruments record < 256 ^ N.of_nat 2)%N /\
      (index_level_type record < 256 ^ N.of_nat 1)%N /\
      (index_price_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (event_time record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (index_level record) ++
      encode_uint_le 8 (pctg_of_capitalization record) ++
      encode_uint_le 8 (prct_varfrom_prev_close record) ++
      encode_uint_le 2 (num_traded_instruments record) ++
      encode_uint 1 (index_level_type record) ++
      encode_uint 1 (index_price_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (emm_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (event_time_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (symbol_index_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (index_level_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (pctg_of_capitalization_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (prct_varfrom_prev_close_value, bytes) =>
                                      match decode_uint_le 2 bytes with
                                      | None => None
                                      | Some (num_traded_instruments_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (index_level_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (index_price_code_value, bytes) =>
                                                  Some ({| md_seq_num := md_seq_num_value; rebroadcast_indicator := rebroadcast_indicator_value; emm := emm_value; event_time := event_time_value; symbol_index := symbol_index_value; index_level := index_level_value; pctg_of_capitalization := pctg_of_capitalization_value; prct_varfrom_prev_close := prct_varfrom_prev_close_value; num_traded_instruments := num_traded_instruments_value; index_level_type := index_level_type_value; index_price_code := index_price_code_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RealTimeIndexMessage.

  Module IndexSummaryMessage.

    (** IndexSummaryMessage *)
    Record t := {
      md_seq_num : N;
      rebroadcast_indicator : N;
      emm : N;
      event_time : N;
      symbol_index : N;
      opening_level : N;
      opening_time : N;
      confirmed_reference_level : N;
      confirmed_reference_time : N;
      closing_reference_level : N;
      closing_reference_time : N;
      prct_varfrom_prev_close : N;
      high_level : N;
      high_time : N;
      low_level : N;
      low_time : N;
      liquidation_level : N;
      liquidation_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (event_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (opening_level record < 256 ^ N.of_nat 8)%N /\
      (opening_time record < 256 ^ N.of_nat 8)%N /\
      (confirmed_reference_level record < 256 ^ N.of_nat 8)%N /\
      (confirmed_reference_time record < 256 ^ N.of_nat 8)%N /\
      (closing_reference_level record < 256 ^ N.of_nat 8)%N /\
      (closing_reference_time record < 256 ^ N.of_nat 8)%N /\
      (prct_varfrom_prev_close record < 256 ^ N.of_nat 8)%N /\
      (high_level record < 256 ^ N.of_nat 8)%N /\
      (high_time record < 256 ^ N.of_nat 8)%N /\
      (low_level record < 256 ^ N.of_nat 8)%N /\
      (low_time record < 256 ^ N.of_nat 8)%N /\
      (liquidation_level record < 256 ^ N.of_nat 8)%N /\
      (liquidation_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (event_time record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (opening_level record) ++
      encode_uint_le 8 (opening_time record) ++
      encode_uint_le 8 (confirmed_reference_level record) ++
      encode_uint_le 8 (confirmed_reference_time record) ++
      encode_uint_le 8 (closing_reference_level record) ++
      encode_uint_le 8 (closing_reference_time record) ++
      encode_uint_le 8 (prct_varfrom_prev_close record) ++
      encode_uint_le 8 (high_level record) ++
      encode_uint_le 8 (high_time record) ++
      encode_uint_le 8 (low_level record) ++
      encode_uint_le 8 (low_time record) ++
      encode_uint_le 8 (liquidation_level record) ++
      encode_uint_le 8 (liquidation_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (emm_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (event_time_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (symbol_index_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (opening_level_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (opening_time_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (confirmed_reference_level_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (confirmed_reference_time_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (closing_reference_level_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (closing_reference_time_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (prct_varfrom_prev_close_value, bytes) =>
                                                      match decode_uint_le 8 bytes with
                                                      | None => None
                                                      | Some (high_level_value, bytes) =>
                                                          match decode_uint_le 8 bytes with
                                                          | None => None
                                                          | Some (high_time_value, bytes) =>
                                                              match decode_uint_le 8 bytes with
                                                              | None => None
                                                              | Some (low_level_value, bytes) =>
                                                                  match decode_uint_le 8 bytes with
                                                                  | None => None
                                                                  | Some (low_time_value, bytes) =>
                                                                      match decode_uint_le 8 bytes with
                                                                      | None => None
                                                                      | Some (liquidation_level_value, bytes) =>
                                                                          match decode_uint_le 8 bytes with
                                                                          | None => None
                                                                          | Some (liquidation_time_value, bytes) =>
                                                                              Some ({| md_seq_num := md_seq_num_value; rebroadcast_indicator := rebroadcast_indicator_value; emm := emm_value; event_time := event_time_value; symbol_index := symbol_index_value; opening_level := opening_level_value; opening_time := opening_time_value; confirmed_reference_level := confirmed_reference_level_value; confirmed_reference_time := confirmed_reference_time_value; closing_reference_level := closing_reference_level_value; closing_reference_time := closing_reference_time_value; prct_varfrom_prev_close := prct_varfrom_prev_close_value; high_level := high_level_value; high_time := high_time_value; low_level := low_level_value; low_time := low_time_value; liquidation_level := liquidation_level_value; liquidation_time := liquidation_time_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 126.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint_le by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End IndexSummaryMessage.

  Module ApaQuotesMessage.

    (** APAQuotesMessage *)
    Record t := {
      md_seq_num_optional : N;
      rebroadcast_indicator : N;
      mifid_instrument_id_type : list byte;
      mifid_instrument_id : list byte;
      mic : list byte;
      currency : list byte;
      lei_code : list byte;
      event_time : N;
      quote_update_type : N;
      mifid_price : list byte;
      mifid_quantity : list byte;
      apa_origin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num_optional record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mifid_instrument_id_type record) = 4 /\
      Datatypes.length (mifid_instrument_id record) = 12 /\
      Datatypes.length (mic record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (lei_code record) = 20 /\
      (event_time record < 256 ^ N.of_nat 8)%N /\
      (quote_update_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mifid_price record) = 20 /\
      Datatypes.length (mifid_quantity record) = 20 /\
      Datatypes.length (apa_origin record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num_optional record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_bytes 4 (mifid_instrument_id_type record) ++
      encode_bytes 12 (mifid_instrument_id record) ++
      encode_bytes 4 (mic record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 20 (lei_code record) ++
      encode_uint_le 8 (event_time record) ++
      encode_uint 1 (quote_update_type record) ++
      encode_bytes 20 (mifid_price record) ++
      encode_bytes 20 (mifid_quantity record) ++
      encode_bytes 4 (apa_origin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_optional_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (mifid_instrument_id_type_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (mifid_instrument_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (mic_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (currency_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (lei_code_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (event_time_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (quote_update_type_value, bytes) =>
                                          match decode_bytes 20 bytes with
                                          | None => None
                                          | Some (mifid_price_value, bytes) =>
                                              match decode_bytes 20 bytes with
                                              | None => None
                                              | Some (mifid_quantity_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (apa_origin_value, bytes) =>
                                                      Some ({| md_seq_num_optional := md_seq_num_optional_value; rebroadcast_indicator := rebroadcast_indicator_value; mifid_instrument_id_type := mifid_instrument_id_type_value; mifid_instrument_id := mifid_instrument_id_value; mic := mic_value; currency := currency_value; lei_code := lei_code_value; event_time := event_time_value; quote_update_type := quote_update_type_value; mifid_price := mifid_price_value; mifid_quantity := mifid_quantity_value; apa_origin := apa_origin_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ApaQuotesMessage.

  Module ApaStandingDataMessage.

    (** APAStandingDataMessage *)
    Record t := {
      md_seq_num_optional : N;
      rebroadcast_indicator : N;
      mifid_instrument_id_type : list byte;
      mifid_instrument_id : list byte;
      full_instrument_name : list byte;
      cfi_optional : list byte;
      notional_currency : list byte;
      second_notional_currency : list byte;
      price_multiplier : N;
      price_multiplier_decimals : N;
      underlying_isin_code : list byte;
      underlying_index_name : list byte;
      underlying_index_term : list byte;
      option_type : N;
      strike_price : N;
      strike_price_decimals : N;
      exer_style : N;
      maturity_date_optional : list byte;
      expiry_date : list byte;
      settlement_method : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num_optional record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mifid_instrument_id_type record) = 4 /\
      Datatypes.length (mifid_instrument_id record) = 12 /\
      Datatypes.length (full_instrument_name record) = 102 /\
      Datatypes.length (cfi_optional record) = 6 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (second_notional_currency record) = 3 /\
      (price_multiplier record < 256 ^ N.of_nat 4)%N /\
      (price_multiplier_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_isin_code record) = 12 /\
      Datatypes.length (underlying_index_name record) = 25 /\
      Datatypes.length (underlying_index_term record) = 8 /\
      (option_type record < 256 ^ N.of_nat 1)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_price_decimals record < 256 ^ N.of_nat 1)%N /\
      (exer_style record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (maturity_date_optional record) = 8 /\
      Datatypes.length (expiry_date record) = 8 /\
      Datatypes.length (settlement_method record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num_optional record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_bytes 4 (mifid_instrument_id_type record) ++
      encode_bytes 12 (mifid_instrument_id record) ++
      encode_bytes 102 (full_instrument_name record) ++
      encode_bytes 6 (cfi_optional record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 3 (second_notional_currency record) ++
      encode_uint_le 4 (price_multiplier record) ++
      encode_uint 1 (price_multiplier_decimals record) ++
      encode_bytes 12 (underlying_isin_code record) ++
      encode_bytes 25 (underlying_index_name record) ++
      encode_bytes 8 (underlying_index_term record) ++
      encode_uint 1 (option_type record) ++
      encode_uint_le 8 (strike_price record) ++
      encode_uint 1 (strike_price_decimals record) ++
      encode_uint 1 (exer_style record) ++
      encode_bytes 8 (maturity_date_optional record) ++
      encode_bytes 8 (expiry_date record) ++
      encode_bytes 1 (settlement_method record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_optional_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (mifid_instrument_id_type_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (mifid_instrument_id_value, bytes) =>
                      match decode_bytes 102 bytes with
                      | None => None
                      | Some (full_instrument_name_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (cfi_optional_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (notional_currency_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (second_notional_currency_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (price_multiplier_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (price_multiplier_decimals_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (underlying_isin_code_value, bytes) =>
                                                  match decode_bytes 25 bytes with
                                                  | None => None
                                                  | Some (underlying_index_name_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (underlying_index_term_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (option_type_value, bytes) =>
                                                              match decode_uint_le 8 bytes with
                                                              | None => None
                                                              | Some (strike_price_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (strike_price_decimals_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (exer_style_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (maturity_date_optional_value, bytes) =>
                                                                              match decode_bytes 8 bytes with
                                                                              | None => None
                                                                              | Some (expiry_date_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (settlement_method_value, bytes) =>
                                                                                      Some ({| md_seq_num_optional := md_seq_num_optional_value; rebroadcast_indicator := rebroadcast_indicator_value; mifid_instrument_id_type := mifid_instrument_id_type_value; mifid_instrument_id := mifid_instrument_id_value; full_instrument_name := full_instrument_name_value; cfi_optional := cfi_optional_value; notional_currency := notional_currency_value; second_notional_currency := second_notional_currency_value; price_multiplier := price_multiplier_value; price_multiplier_decimals := price_multiplier_decimals_value; underlying_isin_code := underlying_isin_code_value; underlying_index_name := underlying_index_name_value; underlying_index_term := underlying_index_term_value; option_type := option_type_value; strike_price := strike_price_value; strike_price_decimals := strike_price_decimals_value; exer_style := exer_style_value; maturity_date_optional := maturity_date_optional_value; expiry_date := expiry_date_value; settlement_method := settlement_method_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 217.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ApaStandingDataMessage.

  Module ApaFullTradeInformationMessage.

    (** APAFullTradeInformationMessage *)
    Record t := {
      md_seq_num : N;
      rebroadcast_indicator : N;
      emm : N;
      event_time : N;
      trading_date_time : list byte;
      publication_date_time : list byte;
      trade_type : N;
      mifid_instrument_id_type_optional : list byte;
      mifid_instrument_id_optional : list byte;
      mifid_transaction_id : list byte;
      mifid_price_optional : list byte;
      mifid_quantity : list byte;
      mifid_price_notation : list byte;
      mifid_currency : list byte;
      mifid_qty_in_msrmt_unit_notation : list byte;
      mifid_quantity_measurement_unit : list byte;
      mifid_notional_amount : list byte;
      notional_currency : list byte;
      mifid_clearing_flag : list byte;
      efficient_mmt_market_mechanism : N;
      efficient_mmt_trading_mode : list byte;
      efficient_mmt_transaction_category : list byte;
      efficient_mmt_negotiation_indicator : list byte;
      efficient_mmt_agency_cross_trade_indicator : list byte;
      efficient_mmt_modification_indicator : list byte;
      efficient_mmt_benchmark_indicator : list byte;
      efficient_mmt_special_dividend_indicator : list byte;
      efficient_mmt_off_book_automated_indicator : list byte;
      efficient_mmt_contributionto_price : list byte;
      efficient_mmt_algorithmic_indicator : list byte;
      efficient_mmt_publication_mode : list byte;
      efficient_mmt_post_trade_deferral : list byte;
      efficient_mmt_duplicative_indicator : list byte;
      trade_reference : list byte;
      original_report_timestamp : N;
      price_multiplier : N;
      price_multiplier_decimals : N;
      venue : list byte;
      mifid_emission_allowance_type : list byte;
      long_trade_reference : list byte;
      apa_origin : list byte;
      trade_unique_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      (emm record < 256 ^ N.of_nat 1)%N /\
      (event_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_date_time record) = 27 /\
      Datatypes.length (publication_date_time record) = 27 /\
      (trade_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mifid_instrument_id_type_optional record) = 4 /\
      Datatypes.length (mifid_instrument_id_optional record) = 12 /\
      Datatypes.length (mifid_transaction_id record) = 52 /\
      Datatypes.length (mifid_price_optional record) = 20 /\
      Datatypes.length (mifid_quantity record) = 20 /\
      Datatypes.length (mifid_price_notation record) = 4 /\
      Datatypes.length (mifid_currency record) = 3 /\
      Datatypes.length (mifid_qty_in_msrmt_unit_notation record) = 25 /\
      Datatypes.length (mifid_quantity_measurement_unit record) = 20 /\
      Datatypes.length (mifid_notional_amount record) = 20 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (mifid_clearing_flag record) = 5 /\
      (efficient_mmt_market_mechanism record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (efficient_mmt_trading_mode record) = 1 /\
      Datatypes.length (efficient_mmt_transaction_category record) = 1 /\
      Datatypes.length (efficient_mmt_negotiation_indicator record) = 1 /\
      Datatypes.length (efficient_mmt_agency_cross_trade_indicator record) = 1 /\
      Datatypes.length (efficient_mmt_modification_indicator record) = 1 /\
      Datatypes.length (efficient_mmt_benchmark_indicator record) = 1 /\
      Datatypes.length (efficient_mmt_special_dividend_indicator record) = 1 /\
      Datatypes.length (efficient_mmt_off_book_automated_indicator record) = 1 /\
      Datatypes.length (efficient_mmt_contributionto_price record) = 1 /\
      Datatypes.length (efficient_mmt_algorithmic_indicator record) = 1 /\
      Datatypes.length (efficient_mmt_publication_mode record) = 1 /\
      Datatypes.length (efficient_mmt_post_trade_deferral record) = 1 /\
      Datatypes.length (efficient_mmt_duplicative_indicator record) = 1 /\
      Datatypes.length (trade_reference record) = 30 /\
      (original_report_timestamp record < 256 ^ N.of_nat 8)%N /\
      (price_multiplier record < 256 ^ N.of_nat 4)%N /\
      (price_multiplier_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (venue record) = 11 /\
      Datatypes.length (mifid_emission_allowance_type record) = 4 /\
      Datatypes.length (long_trade_reference record) = 52 /\
      Datatypes.length (apa_origin record) = 4 /\
      Datatypes.length (trade_unique_identifier record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_uint 1 (emm record) ++
      encode_uint_le 8 (event_time record) ++
      encode_bytes 27 (trading_date_time record) ++
      encode_bytes 27 (publication_date_time record) ++
      encode_uint 1 (trade_type record) ++
      encode_bytes 4 (mifid_instrument_id_type_optional record) ++
      encode_bytes 12 (mifid_instrument_id_optional record) ++
      encode_bytes 52 (mifid_transaction_id record) ++
      encode_bytes 20 (mifid_price_optional record) ++
      encode_bytes 20 (mifid_quantity record) ++
      encode_bytes 4 (mifid_price_notation record) ++
      encode_bytes 3 (mifid_currency record) ++
      encode_bytes 25 (mifid_qty_in_msrmt_unit_notation record) ++
      encode_bytes 20 (mifid_quantity_measurement_unit record) ++
      encode_bytes 20 (mifid_notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 5 (mifid_clearing_flag record) ++
      encode_uint 1 (efficient_mmt_market_mechanism record) ++
      encode_bytes 1 (efficient_mmt_trading_mode record) ++
      encode_bytes 1 (efficient_mmt_transaction_category record) ++
      encode_bytes 1 (efficient_mmt_negotiation_indicator record) ++
      encode_bytes 1 (efficient_mmt_agency_cross_trade_indicator record) ++
      encode_bytes 1 (efficient_mmt_modification_indicator record) ++
      encode_bytes 1 (efficient_mmt_benchmark_indicator record) ++
      encode_bytes 1 (efficient_mmt_special_dividend_indicator record) ++
      encode_bytes 1 (efficient_mmt_off_book_automated_indicator record) ++
      encode_bytes 1 (efficient_mmt_contributionto_price record) ++
      encode_bytes 1 (efficient_mmt_algorithmic_indicator record) ++
      encode_bytes 1 (efficient_mmt_publication_mode record) ++
      encode_bytes 1 (efficient_mmt_post_trade_deferral record) ++
      encode_bytes 1 (efficient_mmt_duplicative_indicator record) ++
      encode_bytes 30 (trade_reference record) ++
      encode_uint_le 8 (original_report_timestamp record) ++
      encode_uint_le 4 (price_multiplier record) ++
      encode_uint 1 (price_multiplier_decimals record) ++
      encode_bytes 11 (venue record) ++
      encode_bytes 4 (mifid_emission_allowance_type record) ++
      encode_bytes 52 (long_trade_reference record) ++
      encode_bytes 4 (apa_origin record) ++
      encode_bytes 16 (trade_unique_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (emm_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (event_time_value, bytes) =>
                      match decode_bytes 27 bytes with
                      | None => None
                      | Some (trading_date_time_value, bytes) =>
                          match decode_bytes 27 bytes with
                          | None => None
                          | Some (publication_date_time_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (mifid_instrument_id_type_optional_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (mifid_instrument_id_optional_value, bytes) =>
                                          match decode_bytes 52 bytes with
                                          | None => None
                                          | Some (mifid_transaction_id_value, bytes) =>
                                              match decode_bytes 20 bytes with
                                              | None => None
                                              | Some (mifid_price_optional_value, bytes) =>
                                                  match decode_bytes 20 bytes with
                                                  | None => None
                                                  | Some (mifid_quantity_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (mifid_price_notation_value, bytes) =>
                                                          match decode_bytes 3 bytes with
                                                          | None => None
                                                          | Some (mifid_currency_value, bytes) =>
                                                              match decode_bytes 25 bytes with
                                                              | None => None
                                                              | Some (mifid_qty_in_msrmt_unit_notation_value, bytes) =>
                                                                  match decode_bytes 20 bytes with
                                                                  | None => None
                                                                  | Some (mifid_quantity_measurement_unit_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (mifid_notional_amount_value, bytes) =>
                                                                          match decode_bytes 3 bytes with
                                                                          | None => None
                                                                          | Some (notional_currency_value, bytes) =>
                                                                              match decode_bytes 5 bytes with
                                                                              | None => None
                                                                              | Some (mifid_clearing_flag_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (efficient_mmt_market_mechanism_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (efficient_mmt_trading_mode_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (efficient_mmt_transaction_category_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (efficient_mmt_negotiation_indicator_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (efficient_mmt_agency_cross_trade_indicator_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (efficient_mmt_modification_indicator_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (efficient_mmt_benchmark_indicator_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (efficient_mmt_special_dividend_indicator_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (efficient_mmt_off_book_automated_indicator_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (efficient_mmt_contributionto_price_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (efficient_mmt_algorithmic_indicator_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (efficient_mmt_publication_mode_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (efficient_mmt_post_trade_deferral_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (efficient_mmt_duplicative_indicator_value, bytes) =>
                                                                                                                                          match decode_bytes 30 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (trade_reference_value, bytes) =>
                                                                                                                                              match decode_uint_le 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (original_report_timestamp_value, bytes) =>
                                                                                                                                                  match decode_uint_le 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (price_multiplier_value, bytes) =>
                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (price_multiplier_decimals_value, bytes) =>
                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (venue_value, bytes) =>
                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (mifid_emission_allowance_type_value, bytes) =>
                                                                                                                                                                  match decode_bytes 52 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (long_trade_reference_value, bytes) =>
                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (apa_origin_value, bytes) =>
                                                                                                                                                                          match decode_bytes 16 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (trade_unique_identifier_value, bytes) =>
                                                                                                                                                                              Some ({| md_seq_num := md_seq_num_value; rebroadcast_indicator := rebroadcast_indicator_value; emm := emm_value; event_time := event_time_value; trading_date_time := trading_date_time_value; publication_date_time := publication_date_time_value; trade_type := trade_type_value; mifid_instrument_id_type_optional := mifid_instrument_id_type_optional_value; mifid_instrument_id_optional := mifid_instrument_id_optional_value; mifid_transaction_id := mifid_transaction_id_value; mifid_price_optional := mifid_price_optional_value; mifid_quantity := mifid_quantity_value; mifid_price_notation := mifid_price_notation_value; mifid_currency := mifid_currency_value; mifid_qty_in_msrmt_unit_notation := mifid_qty_in_msrmt_unit_notation_value; mifid_quantity_measurement_unit := mifid_quantity_measurement_unit_value; mifid_notional_amount := mifid_notional_amount_value; notional_currency := notional_currency_value; mifid_clearing_flag := mifid_clearing_flag_value; efficient_mmt_market_mechanism := efficient_mmt_market_mechanism_value; efficient_mmt_trading_mode := efficient_mmt_trading_mode_value; efficient_mmt_transaction_category := efficient_mmt_transaction_category_value; efficient_mmt_negotiation_indicator := efficient_mmt_negotiation_indicator_value; efficient_mmt_agency_cross_trade_indicator := efficient_mmt_agency_cross_trade_indicator_value; efficient_mmt_modification_indicator := efficient_mmt_modification_indicator_value; efficient_mmt_benchmark_indicator := efficient_mmt_benchmark_indicator_value; efficient_mmt_special_dividend_indicator := efficient_mmt_special_dividend_indicator_value; efficient_mmt_off_book_automated_indicator := efficient_mmt_off_book_automated_indicator_value; efficient_mmt_contributionto_price := efficient_mmt_contributionto_price_value; efficient_mmt_algorithmic_indicator := efficient_mmt_algorithmic_indicator_value; efficient_mmt_publication_mode := efficient_mmt_publication_mode_value; efficient_mmt_post_trade_deferral := efficient_mmt_post_trade_deferral_value; efficient_mmt_duplicative_indicator := efficient_mmt_duplicative_indicator_value; trade_reference := trade_reference_value; original_report_timestamp := original_report_timestamp_value; price_multiplier := price_multiplier_value; price_multiplier_decimals := price_multiplier_decimals_value; venue := venue_value; mifid_emission_allowance_type := mifid_emission_allowance_type_value; long_trade_reference := long_trade_reference_value; apa_origin := apa_origin_value; trade_unique_identifier := trade_unique_identifier_value |}, bytes)
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 405.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 bound_41]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
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
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
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
      rewrite decode_encode_uint_le by exact bound_34.
      rewrite decode_encode_uint_le by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ApaFullTradeInformationMessage.

  Module BfTradeMessage.

    (** BFTradeMessage *)
    Record t := {
      md_seq_num_optional : N;
      rebroadcast_indicator : N;
      symbol_index : N;
      mifid_transaction_id : list byte;
      event_time : N;
      bid_offer_date_time : N;
      mmt_modification_indicator : list byte;
      price : N;
      bid_price : N;
      offer_price : N;
      quantity : N;
      mmt_agency_cross_trade_indicator : list byte;
      mmt_benchmark_indicator : list byte;
      mmt_special_dividend_indicator : list byte;
      mmt_trading_mode : list byte;
      mifid_price_notation : list byte;
      quantity_notation : list byte;
      notional_amount_traded : N;
      trading_currency_optional : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num_optional record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mifid_transaction_id record) = 52 /\
      (event_time record < 256 ^ N.of_nat 8)%N /\
      (bid_offer_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mmt_modification_indicator record) = 4 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (offer_price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mmt_agency_cross_trade_indicator record) = 4 /\
      Datatypes.length (mmt_benchmark_indicator record) = 4 /\
      Datatypes.length (mmt_special_dividend_indicator record) = 4 /\
      Datatypes.length (mmt_trading_mode record) = 1 /\
      Datatypes.length (mifid_price_notation record) = 4 /\
      Datatypes.length (quantity_notation record) = 3 /\
      (notional_amount_traded record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_currency_optional record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num_optional record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_bytes 52 (mifid_transaction_id record) ++
      encode_uint_le 8 (event_time record) ++
      encode_uint_le 8 (bid_offer_date_time record) ++
      encode_bytes 4 (mmt_modification_indicator record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 8 (bid_price record) ++
      encode_uint_le 8 (offer_price record) ++
      encode_uint_le 8 (quantity record) ++
      encode_bytes 4 (mmt_agency_cross_trade_indicator record) ++
      encode_bytes 4 (mmt_benchmark_indicator record) ++
      encode_bytes 4 (mmt_special_dividend_indicator record) ++
      encode_bytes 1 (mmt_trading_mode record) ++
      encode_bytes 4 (mifid_price_notation record) ++
      encode_bytes 3 (quantity_notation record) ++
      encode_uint_le 8 (notional_amount_traded record) ++
      encode_bytes 3 (trading_currency_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_optional_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_bytes 52 bytes with
                  | None => None
                  | Some (mifid_transaction_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (event_time_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (bid_offer_date_time_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (mmt_modification_indicator_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (bid_price_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (offer_price_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (quantity_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (mmt_agency_cross_trade_indicator_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (mmt_benchmark_indicator_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (mmt_special_dividend_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (mmt_trading_mode_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (mifid_price_notation_value, bytes) =>
                                                                      match decode_bytes 3 bytes with
                                                                      | None => None
                                                                      | Some (quantity_notation_value, bytes) =>
                                                                          match decode_uint_le 8 bytes with
                                                                          | None => None
                                                                          | Some (notional_amount_traded_value, bytes) =>
                                                                              match decode_bytes 3 bytes with
                                                                              | None => None
                                                                              | Some (trading_currency_optional_value, bytes) =>
                                                                                  Some ({| md_seq_num_optional := md_seq_num_optional_value; rebroadcast_indicator := rebroadcast_indicator_value; symbol_index := symbol_index_value; mifid_transaction_id := mifid_transaction_id_value; event_time := event_time_value; bid_offer_date_time := bid_offer_date_time_value; mmt_modification_indicator := mmt_modification_indicator_value; price := price_value; bid_price := bid_price_value; offer_price := offer_price_value; quantity := quantity_value; mmt_agency_cross_trade_indicator := mmt_agency_cross_trade_indicator_value; mmt_benchmark_indicator := mmt_benchmark_indicator_value; mmt_special_dividend_indicator := mmt_special_dividend_indicator_value; mmt_trading_mode := mmt_trading_mode_value; mifid_price_notation := mifid_price_notation_value; quantity_notation := quantity_notation_value; notional_amount_traded := notional_amount_traded_value; trading_currency_optional := trading_currency_optional_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BfTradeMessage.

  Module BfnavMessage.

    (** BFNAVMessage *)
    Record t := {
      md_seq_num_optional : N;
      rebroadcast_indicator : N;
      symbol_index : N;
      bid_offer_date_time : N;
      mifid_transaction_id : list byte;
      mmt_modification_indicator : list byte;
      nav_price : N;
      event_time_optional : N;
      nav_bid_price : N;
      nav_offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num_optional record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (bid_offer_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mifid_transaction_id record) = 52 /\
      Datatypes.length (mmt_modification_indicator record) = 4 /\
      (nav_price record < 256 ^ N.of_nat 8)%N /\
      (event_time_optional record < 256 ^ N.of_nat 8)%N /\
      (nav_bid_price record < 256 ^ N.of_nat 8)%N /\
      (nav_offer_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num_optional record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (bid_offer_date_time record) ++
      encode_bytes 52 (mifid_transaction_id record) ++
      encode_bytes 4 (mmt_modification_indicator record) ++
      encode_uint_le 8 (nav_price record) ++
      encode_uint_le 8 (event_time_optional record) ++
      encode_uint_le 8 (nav_bid_price record) ++
      encode_uint_le 8 (nav_offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_optional_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (bid_offer_date_time_value, bytes) =>
                      match decode_bytes 52 bytes with
                      | None => None
                      | Some (mifid_transaction_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (mmt_modification_indicator_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (nav_price_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (event_time_optional_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (nav_bid_price_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (nav_offer_price_value, bytes) =>
                                              Some ({| md_seq_num_optional := md_seq_num_optional_value; rebroadcast_indicator := rebroadcast_indicator_value; symbol_index := symbol_index_value; bid_offer_date_time := bid_offer_date_time_value; mifid_transaction_id := mifid_transaction_id_value; mmt_modification_indicator := mmt_modification_indicator_value; nav_price := nav_price_value; event_time_optional := event_time_optional_value; nav_bid_price := nav_bid_price_value; nav_offer_price := nav_offer_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BfnavMessage.

  Module BfInstrumentSuspensionMessage.

    (** BFInstrumentSuspensionMessage *)
    Record t := {
      md_seq_num_optional : N;
      rebroadcast_indicator : N;
      symbol_index : N;
      event_time : N;
      security_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_seq_num_optional record < 256 ^ N.of_nat 8)%N /\
      (rebroadcast_indicator record < 256 ^ N.of_nat 1)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (event_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (md_seq_num_optional record) ++
      encode_uint 1 (rebroadcast_indicator record) ++
      encode_uint_le 4 (symbol_index record) ++
      encode_uint_le 8 (event_time record) ++
      encode_bytes 1 (security_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (md_seq_num_optional_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rebroadcast_indicator_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (event_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (security_condition_value, bytes) =>
                          Some ({| md_seq_num_optional := md_seq_num_optional_value; rebroadcast_indicator := rebroadcast_indicator_value; symbol_index := symbol_index_value; event_time := event_time_value; security_condition := security_condition_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BfInstrumentSuspensionMessage.

  Module StartOfSnapshotMessage.

    (** StartOfSnapshotMessage *)
    Record t := {
      last_md_seq_num : N;
      snapshot_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (snapshot_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (last_md_seq_num record) ++
      encode_uint_le 8 (snapshot_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (last_md_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (snapshot_time_value, bytes) =>
              Some ({| last_md_seq_num := last_md_seq_num_value; snapshot_time := snapshot_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StartOfSnapshotMessage.

  Module EndOfSnapshotMessage.

    (** EndOfSnapshotMessage *)
    Record t := {
      last_md_seq_num : N;
      snapshot_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_md_seq_num record < 256 ^ N.of_nat 8)%N /\
      (snapshot_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (last_md_seq_num record) ++
      encode_uint_le 8 (snapshot_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (last_md_seq_num_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (snapshot_time_value, bytes) =>
              Some ({| last_md_seq_num := last_md_seq_num_value; snapshot_time := snapshot_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EndOfSnapshotMessage.

End EuronextOptiqMarketDataGatewayV524.
