From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Deep Feed

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
      - a Composite rule
      - a run filling what frames it
      - a run counted by a field
      - a field present only on a condition
  *)

Module ArcaOptionsDeepFeedV12M.

  Module MessageHeader.

    (** Pillar message header *)
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

  Module SequenceNumberResetMessage.

    (** Sent to reset the Message Sequence Number at start of day, or in response to failure recoveries. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      product_id : N;
      channel_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; product_id := product_id_value; channel_id := channel_id_value |}, bytes)
                  end
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

  End SequenceNumberResetMessage.

  Module SourceTimeReferenceMessage.

    (** Sent at the start of every second during periods of active data publication. *)
    Record t := {
      id : N;
      symbol_seq_num : N;
      source_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (id record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (source_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_time_value, bytes) =>
                  Some ({| id := id_value; symbol_seq_num := symbol_seq_num_value; source_time := source_time_value |}, bytes)
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

  End SourceTimeReferenceMessage.

  Module SymbolIndexMappingMessage.

    (** Published over the real-time data channels at system startup or in the context of a refresh sequence. Provides referential data for a single specified symbol or underlying symbol. *)
    Record t := {
      symbol_index : N;
      symbol : list byte;
      reserved_1 : N;
      market_id : N;
      system_id : N;
      exchange_code : list byte;
      price_scale_code : N;
      security_type : list byte;
      lot_size : N;
      prev_close_price : N;
      prev_close_volume : N;
      price_resolution : N;
      round_lot : list byte;
      reserved_2 : N;
      second_reserved_2 : N;
      third_reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 11 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 2)%N /\
      (system_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exchange_code record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_type record) = 1 /\
      (lot_size record < 256 ^ N.of_nat 2)%N /\
      (prev_close_price record < 256 ^ N.of_nat 4)%N /\
      (prev_close_volume record < 256 ^ N.of_nat 4)%N /\
      (price_resolution record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (round_lot record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (second_reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (third_reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_bytes 11 (symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (market_id record) ++
      encode_uint 1 (system_id record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 1 (security_type record) ++
      encode_uint 2 (lot_size record) ++
      encode_uint 4 (prev_close_price record) ++
      encode_uint 4 (prev_close_volume record) ++
      encode_uint 1 (price_resolution record) ++
      encode_bytes 1 (round_lot record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 2 (second_reserved_2 record) ++
      encode_uint 2 (third_reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (system_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (exchange_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (price_scale_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (security_type_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (lot_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (prev_close_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (prev_close_volume_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (price_resolution_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (round_lot_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (reserved_2_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (second_reserved_2_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (third_reserved_2_value, bytes) =>
                                                                      Some ({| symbol_index := symbol_index_value; symbol := symbol_value; reserved_1 := reserved_1_value; market_id := market_id_value; system_id := system_id_value; exchange_code := exchange_code_value; price_scale_code := price_scale_code_value; security_type := security_type_value; lot_size := lot_size_value; prev_close_price := prev_close_price_value; prev_close_volume := prev_close_volume_value; price_resolution := price_resolution_value; round_lot := round_lot_value; reserved_2 := reserved_2_value; second_reserved_2 := second_reserved_2_value; third_reserved_2 := third_reserved_2_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolIndexMappingMessage.

  Module SymbolClearMessage.

    (** In case of a failure and recovery, the publisher may send a full state refresh for every symbol or series affected, preceded by a Symbol Clear message. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      next_source_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (next_source_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (next_source_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (next_source_seq_num_value, bytes) =>
                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; next_source_seq_num := next_source_seq_num_value |}, bytes)
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

  End SymbolClearMessage.

  Module SecurityStatusMessage.

    (** Informs clients of changes in the status of a specific security or underlying symbol, such as Trading Halts, Short Sale Restriction state changes, etc. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      security_status : list byte;
      halt_condition : list byte;
      reserved_4 : N;
      price_1 : N;
      price_2 : N;
      ssr_triggering_exchange_id : list byte;
      ssr_triggering_volume : N;
      time : N;
      ssr_state : list byte;
      market_state : list byte;
      session_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_condition record) = 1 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      (price_1 record < 256 ^ N.of_nat 4)%N /\
      (price_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ssr_triggering_exchange_id record) = 1 /\
      (ssr_triggering_volume record < 256 ^ N.of_nat 4)%N /\
      (time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ssr_state record) = 1 /\
      Datatypes.length (market_state record) = 1 /\
      Datatypes.length (session_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (security_status record) ++
      encode_bytes 1 (halt_condition record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_uint 4 (price_1 record) ++
      encode_uint 4 (price_2 record) ++
      encode_bytes 1 (ssr_triggering_exchange_id record) ++
      encode_uint 4 (ssr_triggering_volume record) ++
      encode_uint 4 (time record) ++
      encode_bytes 1 (ssr_state record) ++
      encode_bytes 1 (market_state record) ++
      encode_bytes 1 (session_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (security_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (halt_condition_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (reserved_4_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_1_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (price_2_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ssr_triggering_exchange_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (ssr_triggering_volume_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (time_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (ssr_state_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (market_state_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (session_state_value, bytes) =>
                                                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; security_status := security_status_value; halt_condition := halt_condition_value; reserved_4 := reserved_4_value; price_1 := price_1_value; price_2 := price_2_value; ssr_triggering_exchange_id := ssr_triggering_exchange_id_value; ssr_triggering_volume := ssr_triggering_volume_value; time := time_value; ssr_state := ssr_state_value; market_state := market_state_value; session_state := session_state_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityStatusMessage.

  Module OutrightSeriesIndexMappingMessage.

    (** Published over the real-time data channels at system startup or in the context of a refresh sequence. Provides referential data for a single specified options outright series. *)
    Record t := {
      series_index : N;
      series_type : N;
      market_id : N;
      system_id : N;
      option_symbol_root : list byte;
      underlying_symbol : list byte;
      underlying_index : N;
      price_scale_code : N;
      contract_multiplier : N;
      maturity_date : list byte;
      put_or_call : N;
      strike_price : list byte;
      closing_only_indicator : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_type record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 2)%N /\
      (system_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (option_symbol_root record) = 6 /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (underlying_index record < 256 ^ N.of_nat 4)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (maturity_date record) = 6 /\
      (put_or_call record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (strike_price record) = 10 /\
      Datatypes.length (closing_only_indicator record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (series_index record) ++
      encode_uint 1 (series_type record) ++
      encode_uint 2 (market_id record) ++
      encode_uint 1 (system_id record) ++
      encode_bytes 6 (option_symbol_root record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint 4 (underlying_index record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 2 (contract_multiplier record) ++
      encode_bytes 6 (maturity_date record) ++
      encode_uint 1 (put_or_call record) ++
      encode_bytes 10 (strike_price record) ++
      encode_bytes 1 (closing_only_indicator record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (series_index_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (series_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (market_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (system_id_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (option_symbol_root_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (underlying_symbol_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (underlying_index_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (price_scale_code_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (contract_multiplier_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (maturity_date_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (put_or_call_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (strike_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (closing_only_indicator_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (reserved_1_value, bytes) =>
                                                              Some ({| series_index := series_index_value; series_type := series_type_value; market_id := market_id_value; system_id := system_id_value; option_symbol_root := option_symbol_root_value; underlying_symbol := underlying_symbol_value; underlying_index := underlying_index_value; price_scale_code := price_scale_code_value; contract_multiplier := contract_multiplier_value; maturity_date := maturity_date_value; put_or_call := put_or_call_value; strike_price := strike_price_value; closing_only_indicator := closing_only_indicator_value; reserved_1 := reserved_1_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightSeriesIndexMappingMessage.

  Module OptionsStatusMessage.

    (** Informs clients of changes in the status of a specific option outright series and complex series, such as Trading Halts. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      series_status : list byte;
      market_state : list byte;
      options_status_halt_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (market_state record) = 1 /\
      Datatypes.length (options_status_halt_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 1 (market_state record) ++
      encode_bytes 1 (options_status_halt_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (series_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (series_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (market_state_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (options_status_halt_condition_value, bytes) =>
                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; series_status := series_status_value; market_state := market_state_value; options_status_halt_condition := options_status_halt_condition_value |}, bytes)
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsStatusMessage.

  Module RetransmissionRequestMessage.

    (** Sent by clients via TCP/IP to request retransmission of missed messages. *)
    Record t := {
      begin_seq_num : N;
      end_seq_num : N;
      source_id : list byte;
      product_id : N;
      channel_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (source_id record) = 10 /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record) ++
      encode_bytes 10 (source_id record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_seq_num_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (source_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (product_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (channel_id_value, bytes) =>
                          Some ({| begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value; source_id := source_id_value; product_id := product_id_value; channel_id := channel_id_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmissionRequestMessage.

  Module RefreshRequestMessage.

    (** Sent by clients via TCP/IP to request a refresh of the state of one or all symbols in a specific channel. *)
    Record t := {
      symbol_index : N;
      source_id : list byte;
      product_id : N;
      channel_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (source_id record) = 10 /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_bytes 10 (source_id record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (source_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      Some ({| symbol_index := symbol_index_value; source_id := source_id_value; product_id := product_id_value; channel_id := channel_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshRequestMessage.

  Module SymbolIndexMappingRequestMessage.

    (** Sent by clients via TCP/IP requesting the Symbol Index Mapping messages for one or all symbols in a specified channel. *)
    Record t := {
      symbol_index : N;
      source_id : list byte;
      product_id : N;
      channel_id : N;
      retransmit_method : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (source_id record) = 10 /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N /\
      (retransmit_method record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_bytes 10 (source_id record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record) ++
      encode_uint 1 (retransmit_method record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (source_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (retransmit_method_value, bytes) =>
                          Some ({| symbol_index := symbol_index_value; source_id := source_id_value; product_id := product_id_value; channel_id := channel_id_value; retransmit_method := retransmit_method_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End SymbolIndexMappingRequestMessage.

  Module MessageUnavailableMessage.

    (** Sent over the Retransmission multicast channels to inform clients of unavailability of a range of messages. *)
    Record t := {
      begin_seq_num : N;
      end_seq_num : N;
      product_id : N;
      channel_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_seq_num_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      Some ({| begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value; product_id := product_id_value; channel_id := channel_id_value |}, bytes)
                  end
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

  End MessageUnavailableMessage.

  Module RequestResponseMessage.

    (** Sent immediately via TCP/IP in response to the client's request for retransmission, refresh or Symbol Mapping messages. *)
    Record t := {
      request_seq_num : N;
      begin_seq_num : N;
      end_seq_num : N;
      source_id : list byte;
      product_id : N;
      channel_id : N;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_seq_num record < 256 ^ N.of_nat 4)%N /\
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (source_id record) = 10 /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_seq_num record) ++
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record) ++
      encode_bytes 10 (source_id record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (begin_seq_num_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (end_seq_num_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (source_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (product_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (channel_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (status_value, bytes) =>
                                  Some ({| request_seq_num := request_seq_num_value; begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value; source_id := source_id_value; product_id := product_id_value; channel_id := channel_id_value; status := status_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RequestResponseMessage.

  Module HeartbeatResponseMessage.

    (** Clients who remain connected to the Retransmission Server intraday must respond to a Heartbeat with a Heartbeat Response message within 5 seconds. *)
    Record t := {
      source_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source_id record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (source_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (source_id_value, bytes) =>
          Some ({| source_id := source_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End HeartbeatResponseMessage.

  Module OptionsAddOrderMessage.

    (** Published when a new visible order has been received and added to the book. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      firm_id : list byte;
      reserved_1 : N;
      cust_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (firm_id record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (cust_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 5 (firm_id record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (cust_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (firm_id_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reserved_1_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cust_indicator_value, bytes) =>
                                              Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; firm_id := firm_id_value; reserved_1 := reserved_1_value; cust_indicator := cust_indicator_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsAddOrderMessage.

  Module OptionsModifyOrderMessage.

    (** Sent when the price or volume of an order is changed due to an event other than a cancel-replace, or full or partial execution. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      position_change : N;
      side : list byte;
      cust_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (position_change record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (cust_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (position_change record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (cust_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (position_change_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (cust_indicator_value, bytes) =>
                                          Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; position_change := position_change_value; side := side_value; cust_indicator := cust_indicator_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsModifyOrderMessage.

  Module OptionsDeleteOrderMessage.

    (** Published when an order is taken off of the book for any reason except for full execution. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      order_id : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; order_id := order_id_value; reserved_1 := reserved_1_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End OptionsDeleteOrderMessage.

  Module OptionsOrderExecutionMessage.

    (** Sent when an order is partially or fully executed. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      order_id : N;
      trade_id : N;
      price : N;
      volume : N;
      printable_flag : N;
      reserved_1 : N;
      trade_cond_1 : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (printable_flag record < 256 ^ N.of_nat 1)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (printable_flag record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (printable_flag_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reserved_1_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_cond_1_value, bytes) =>
                                              match decode_uint 3 bytes with
                                              | None => None
                                              | Some (reserved_3_value, bytes) =>
                                                  Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; order_id := order_id_value; trade_id := trade_id_value; price := price_value; volume := volume_value; printable_flag := printable_flag_value; reserved_1 := reserved_1_value; trade_cond_1 := trade_cond_1_value; reserved_3 := reserved_3_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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

  End OptionsOrderExecutionMessage.

  Module OptionsReplaceOrderMessage.

    (** Published when a cancel/replace order is received. The resting order is replaced with a new order containing the same outright or complex series, side and attribution, a new Order ID, and the price and size specified. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      order_id : N;
      new_order_id : N;
      price : N;
      volume : N;
      side : list byte;
      reserved_1 : N;
      cust_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (new_order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (cust_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (new_order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (cust_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (new_order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reserved_1_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cust_indicator_value, bytes) =>
                                              Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; order_id := order_id_value; new_order_id := new_order_id_value; price := price_value; volume := volume_value; side := side_value; reserved_1 := reserved_1_value; cust_indicator := cust_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsReplaceOrderMessage.

  Module OptionsImbalanceMessage.

    (** Published every 5 seconds, during opening and re-opening auctions to update price and volume information. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      reserved_4 : N;
      paired_qty : N;
      total_imbalance_qty : N;
      market_imbalance_qty : N;
      reserved_2 : N;
      auction_type : list byte;
      imbalance_side : list byte;
      continuous_book_clearing_price : N;
      auction_interest_clearing_price : N;
      second_reserved_4 : N;
      indicative_match_price : N;
      upper_collar : N;
      lower_collar : N;
      auction_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      (paired_qty record < 256 ^ N.of_nat 4)%N /\
      (total_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (market_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (imbalance_side record) = 1 /\
      (continuous_book_clearing_price record < 256 ^ N.of_nat 4)%N /\
      (auction_interest_clearing_price record < 256 ^ N.of_nat 4)%N /\
      (second_reserved_4 record < 256 ^ N.of_nat 4)%N /\
      (indicative_match_price record < 256 ^ N.of_nat 4)%N /\
      (upper_collar record < 256 ^ N.of_nat 4)%N /\
      (lower_collar record < 256 ^ N.of_nat 4)%N /\
      (auction_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_uint 4 (paired_qty record) ++
      encode_uint 4 (total_imbalance_qty record) ++
      encode_uint 4 (market_imbalance_qty record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (imbalance_side record) ++
      encode_uint 4 (continuous_book_clearing_price record) ++
      encode_uint 4 (auction_interest_clearing_price record) ++
      encode_uint 4 (second_reserved_4 record) ++
      encode_uint 4 (indicative_match_price record) ++
      encode_uint 4 (upper_collar record) ++
      encode_uint 4 (lower_collar record) ++
      encode_uint 1 (auction_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (series_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (reserved_4_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (paired_qty_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (total_imbalance_qty_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (market_imbalance_qty_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (reserved_2_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (auction_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (imbalance_side_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (continuous_book_clearing_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (auction_interest_clearing_price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (second_reserved_4_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (indicative_match_price_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (upper_collar_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (lower_collar_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (auction_status_value, bytes) =>
                                                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; reserved_4 := reserved_4_value; paired_qty := paired_qty_value; total_imbalance_qty := total_imbalance_qty_value; market_imbalance_qty := market_imbalance_qty_value; reserved_2 := reserved_2_value; auction_type := auction_type_value; imbalance_side := imbalance_side_value; continuous_book_clearing_price := continuous_book_clearing_price_value; auction_interest_clearing_price := auction_interest_clearing_price_value; second_reserved_4 := second_reserved_4_value; indicative_match_price := indicative_match_price_value; upper_collar := upper_collar_value; lower_collar := lower_collar_value; auction_status := auction_status_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsImbalanceMessage.

  Module OptionsAddOrderRefreshMessage.

    (** Sent as part of a refresh response for every order currently resting on the book. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      firm_id : list byte;
      reserved_1 : N;
      cust_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (firm_id record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (cust_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 5 (firm_id record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (cust_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (series_seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (firm_id_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (reserved_1_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cust_indicator_value, bytes) =>
                                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; firm_id := firm_id_value; reserved_1 := reserved_1_value; cust_indicator := cust_indicator_value |}, bytes)
                                              end
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsAddOrderRefreshMessage.

  Module OptionsSeriesRfqMessage.

    (** Published for outright series. Generated by the matching engine to solicit interest in an auction or order. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      rfq_side : list byte;
      type : list byte;
      capacity : list byte;
      total_quantity : N;
      working_price : N;
      participant : N;
      auction_id : N;
      rfq_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (rfq_side record) = 1 /\
      Datatypes.length (type record) = 1 /\
      Datatypes.length (capacity record) = 1 /\
      (total_quantity record < 256 ^ N.of_nat 4)%N /\
      (working_price record < 256 ^ N.of_nat 4)%N /\
      (participant record < 256 ^ N.of_nat 4)%N /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (rfq_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_bytes 1 (rfq_side record) ++
      encode_bytes 1 (type record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 4 (total_quantity record) ++
      encode_uint 4 (working_price record) ++
      encode_uint 4 (participant record) ++
      encode_uint 8 (auction_id record) ++
      encode_bytes 1 (rfq_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (series_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (rfq_side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (type_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (capacity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (total_quantity_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (working_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (participant_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (auction_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (rfq_status_value, bytes) =>
                                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; rfq_side := rfq_side_value; type := type_value; capacity := capacity_value; total_quantity := total_quantity_value; working_price := working_price_value; participant := participant_value; auction_id := auction_id_value; rfq_status := rfq_status_value |}, bytes)
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsSeriesRfqMessage.

  Module OptionsNonDisplayedTradeMessage.

    (** Published as a result of a match between two non-displayed orders. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      trade_id : N;
      price : N;
      volume : N;
      printable_flag : N;
      non_displayed_trade_trade_cond_1 : list byte;
      reserved_3 : N;
      price_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (printable_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (non_displayed_trade_trade_cond_1 record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N /\
      (price_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (printable_flag record) ++
      encode_bytes 1 (non_displayed_trade_trade_cond_1 record) ++
      encode_uint 3 (reserved_3 record) ++
      encode_uint 1 (price_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (printable_flag_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (non_displayed_trade_trade_cond_1_value, bytes) =>
                                      match decode_uint 3 bytes with
                                      | None => None
                                      | Some (reserved_3_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (price_type_value, bytes) =>
                                              Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; trade_id := trade_id_value; price := price_value; volume := volume_value; printable_flag := printable_flag_value; non_displayed_trade_trade_cond_1 := non_displayed_trade_trade_cond_1_value; reserved_3 := reserved_3_value; price_type := price_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsNonDisplayedTradeMessage.

  Module OptionsCrossTradeMessage.

    (** Published on completion of a crossing from the opening and re-opening auction, showing the bulk volume that traded in the auction. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      cross_id : N;
      price : N;
      volume : N;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (cross_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cross_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cross_type_value, bytes) =>
                                  Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; cross_id := cross_id_value; price := price_value; volume := volume_value; cross_type := cross_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsCrossTradeMessage.

  Module OptionsTradeCancelMessage.

    (** Published when an earlier trade has been reported in error. *)
    Record t := {
      source_time_ns : N;
      series_index : N;
      series_seq_num : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (series_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (series_seq_num record) ++
      encode_uint 4 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (series_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      Some ({| source_time_ns := source_time_ns_value; series_index := series_index_value; series_seq_num := series_seq_num_value; trade_id := trade_id_value |}, bytes)
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

  End OptionsTradeCancelMessage.

  Module OptionsOutrightSeriesSummaryMessage.

    (** Published every 60 seconds on a separate multicast channel. Provides high, low, open, close and total volume per series. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      high_price : N;
      low_price : N;
      open : N;
      close : N;
      total_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (open record < 256 ^ N.of_nat 4)%N /\
      (close record < 256 ^ N.of_nat 4)%N /\
      (total_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (high_price record) ++
      encode_uint 4 (low_price record) ++
      encode_uint 4 (open record) ++
      encode_uint 4 (close record) ++
      encode_uint 4 (total_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (open_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (close_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (total_volume_value, bytes) =>
                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; high_price := high_price_value; low_price := low_price_value; open := open_value; close := close_value; total_volume := total_volume_value |}, bytes)
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

  End OptionsOutrightSeriesSummaryMessage.

End ArcaOptionsDeepFeedV12M.
