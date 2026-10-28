From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Trades

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
      - a field present only on a condition
  *)

Module ArcaEquitiesTradesV26A.

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

    (** This message is sent to reset the Message Sequence Number at start of day, or in response to failures. *)
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

    (** For high-volume feeds, this message is sent at the start of every second during periods of active data publication. The client can concatenate the SourceTime field with the SourceTimeNS field in subsequent market data messages to get full 8-byte Matching Engine event timestamps. *)
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

    (** This message is published over the real-time data channels at system startup or in the context of a refresh sequence after a Matching Engine or Pillar Publisher failover. It provides referential data for a single specified symbol. *)
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
      mpv : N;
      unit_of_trade : N;
      reserved_2 : N;
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
      (mpv record < 256 ^ N.of_nat 2)%N /\
      (unit_of_trade record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

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
      encode_uint 2 (mpv record) ++
      encode_uint 2 (unit_of_trade record) ++
      encode_uint 2 (reserved_2 record).

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
                                                          | Some (mpv_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (unit_of_trade_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (reserved_2_value, bytes) =>
                                                                      Some ({| symbol_index := symbol_index_value; symbol := symbol_value; reserved_1 := reserved_1_value; market_id := market_id_value; system_id := system_id_value; exchange_code := exchange_code_value; price_scale_code := price_scale_code_value; security_type := security_type_value; lot_size := lot_size_value; prev_close_price := prev_close_price_value; prev_close_volume := prev_close_volume_value; price_resolution := price_resolution_value; round_lot := round_lot_value; mpv := mpv_value; unit_of_trade := unit_of_trade_value; reserved_2 := reserved_2_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    (** In case of a failure and recovery of a Matching Engine or an Pillar Publisher, the publisher may send a full state refresh for every symbol affected. This unrequested refresh is preceded by a Symbol Clear message. The client should react to receipt of a Symbol Clear message by clearing all state information for the specified symbol in anticipation of receiving a full state refresh. *)
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

    (** This message informs clients of changes in the status of a specific security, such as Trading Halts, Short Sale Restriction state changes, etc. *)
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

  Module RetransmissionRequestMessage.

    (** Clients who have experienced a sequence number gap and need a retransmission of the missed messages should send a Retransmission Request message via TCP to the Request Controller. *)
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

  Module SymbolIndexMappingRequestMessage.

    (** This message is sent by clients via TCP/IP requesting the Symbol Index Mapping messages for one or all symbols in a specified channel. *)
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

  Module RefreshRequestMessage.

    (** Clients who have experienced a failure and need a refresh of the state of one or all symbols in a specific channel should send a Refresh Request message via TCP to the Request Controller. *)
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

  Module MessageUnavailableMessage.

    (** This message will be sent over the Retransmission multicast channels to inform clients of unavailability of a range of messages (or part of a range) for which they may have requested a retransmission. *)
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

    (** This message will be sent immediately via TCP/IP in response to the client's request for retransmission, refresh or Symbol Mapping messages. *)
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

    (** Clients who remain connected to the Retransmission Server intraday must respond to a Heartbeat with a Heartbeat Response message within 5 seconds. If no timely client response is received, the connection will be closed. *)
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

  Module TradeMessage.

    (** A Trade message is sent when there is an execution on the order book. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      volume : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      trade_cond_3 : list byte;
      trade_cond_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      Datatypes.length (trade_cond_3 record) = 1 /\
      Datatypes.length (trade_cond_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_bytes 1 (trade_cond_3 record) ++
      encode_bytes 1 (trade_cond_4 record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_cond_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_2_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_cond_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trade_cond_4_value, bytes) =>
                                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; volume := volume_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; trade_cond_3 := trade_cond_3_value; trade_cond_4 := trade_cond_4_value |}, bytes)
                                              end
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module TradeCancelMessage.

    (** In the event that an earlier trade has been reported in error, a Trade Cancel message is sent. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      original_trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (original_trade_id record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_id_value, bytes) =>
                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; original_trade_id := original_trade_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End TradeCancelMessage.

  Module TradeCorrectionMessage.

    (** In the event that an earlier trade has been reported with one or multiple fields in error, a Trade Correction message is sent. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      original_trade_id : N;
      trade_id : N;
      price : N;
      volume : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      trade_cond_3 : list byte;
      trade_cond_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      Datatypes.length (trade_cond_3 record) = 1 /\
      Datatypes.length (trade_cond_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (original_trade_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_bytes 1 (trade_cond_3 record) ++
      encode_bytes 1 (trade_cond_4 record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_1_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_cond_2_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trade_cond_3_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trade_cond_4_value, bytes) =>
                                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; original_trade_id := original_trade_id_value; trade_id := trade_id_value; price := price_value; volume := volume_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; trade_cond_3 := trade_cond_3_value; trade_cond_4 := trade_cond_4_value |}, bytes)
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module StockSummaryMessage.

    (** The stock summary message is sent every 1 minute on a separate channel from the main trades feed. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
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
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (open record < 256 ^ N.of_nat 4)%N /\
      (close record < 256 ^ N.of_nat 4)%N /\
      (total_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
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
              | Some (symbol_index_value, bytes) =>
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
                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; high_price := high_price_value; low_price := low_price_value; open := open_value; close := close_value; total_volume := total_volume_value |}, bytes)
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

  End StockSummaryMessage.

  Module TrfFractionalTradeMessage.

    (** TRF Fractional Trade Message. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      fractional_volume : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      trade_cond_3 : list byte;
      trade_cond_4 : list byte;
      exec_day_time : N;
      exec_day_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (fractional_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      Datatypes.length (trade_cond_3 record) = 1 /\
      Datatypes.length (trade_cond_4 record) = 1 /\
      (exec_day_time record < 256 ^ N.of_nat 4)%N /\
      (exec_day_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (fractional_volume record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_bytes 1 (trade_cond_3 record) ++
      encode_bytes 1 (trade_cond_4 record) ++
      encode_uint 4 (exec_day_time record) ++
      encode_uint 4 (exec_day_time_ns record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (fractional_volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_cond_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_2_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_cond_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trade_cond_4_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (exec_day_time_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (exec_day_time_ns_value, bytes) =>
                                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; fractional_volume := fractional_volume_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; trade_cond_3 := trade_cond_3_value; trade_cond_4 := trade_cond_4_value; exec_day_time := exec_day_time_value; exec_day_time_ns := exec_day_time_ns_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TrfFractionalTradeMessage.

  Module TrfTradeCancelMessage.

    (** TRF Trade Cancel Message. Same structure as Trade Cancel Message (221). *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      original_trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (original_trade_id record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_id_value, bytes) =>
                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; original_trade_id := original_trade_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End TrfTradeCancelMessage.

  Module TrfFractionalTradeCorrectionMessage.

    (** TRF Fractional Trade Correction Message. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      original_trade_id : N;
      trade_id : N;
      price : N;
      fractional_volume : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      trade_cond_3 : list byte;
      trade_cond_4 : list byte;
      exec_day_time : N;
      exec_day_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (fractional_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      Datatypes.length (trade_cond_3 record) = 1 /\
      Datatypes.length (trade_cond_4 record) = 1 /\
      (exec_day_time record < 256 ^ N.of_nat 4)%N /\
      (exec_day_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (original_trade_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (fractional_volume record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_bytes 1 (trade_cond_3 record) ++
      encode_bytes 1 (trade_cond_4 record) ++
      encode_uint 4 (exec_day_time record) ++
      encode_uint 4 (exec_day_time_ns record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (fractional_volume_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_1_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_cond_2_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trade_cond_3_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trade_cond_4_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (exec_day_time_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (exec_day_time_ns_value, bytes) =>
                                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; original_trade_id := original_trade_id_value; trade_id := trade_id_value; price := price_value; fractional_volume := fractional_volume_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; trade_cond_3 := trade_cond_3_value; trade_cond_4 := trade_cond_4_value; exec_day_time := exec_day_time_value; exec_day_time_ns := exec_day_time_ns_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TrfFractionalTradeCorrectionMessage.

  Module TrfFractionalPriorDayTradeMessage.

    (** If a TRF participant firm fails to report a trade on the day in which it occurs, the firm may report the trade on a subsequent day by publishing a Prior Day Trade message. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      fractional_volume : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      trade_cond_3 : list byte;
      trade_cond_4 : list byte;
      prior_day_time : N;
      prior_day_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (fractional_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      Datatypes.length (trade_cond_3 record) = 1 /\
      Datatypes.length (trade_cond_4 record) = 1 /\
      (prior_day_time record < 256 ^ N.of_nat 4)%N /\
      (prior_day_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (fractional_volume record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_bytes 1 (trade_cond_3 record) ++
      encode_bytes 1 (trade_cond_4 record) ++
      encode_uint 4 (prior_day_time record) ++
      encode_uint 4 (prior_day_time_ns record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (fractional_volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_cond_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_2_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_cond_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trade_cond_4_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (prior_day_time_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (prior_day_time_ns_value, bytes) =>
                                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; fractional_volume := fractional_volume_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; trade_cond_3 := trade_cond_3_value; trade_cond_4 := trade_cond_4_value; prior_day_time := prior_day_time_value; prior_day_time_ns := prior_day_time_ns_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TrfFractionalPriorDayTradeMessage.

  Module TrfFractionalPriorDayTradeCancelMessage.

    (** If a TRF participant firm discovers that it has reported a trade with an inaccurate price or volume on a previous day, the firm may correct the trade on a subsequent day by publishing a Prior Day Trade Cancel message, followed by a Prior Day Trade. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      fractional_volume : N;
      prior_day_time : N;
      prior_day_time_ns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (fractional_volume record < 256 ^ N.of_nat 8)%N /\
      (prior_day_time record < 256 ^ N.of_nat 4)%N /\
      (prior_day_time_ns record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (fractional_volume record) ++
      encode_uint 4 (prior_day_time record) ++
      encode_uint 4 (prior_day_time_ns record).

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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (fractional_volume_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (prior_day_time_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (prior_day_time_ns_value, bytes) =>
                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; fractional_volume := fractional_volume_value; prior_day_time := prior_day_time_value; prior_day_time_ns := prior_day_time_ns_value |}, bytes)
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

  End TrfFractionalPriorDayTradeCancelMessage.

End ArcaEquitiesTradesV26A.
