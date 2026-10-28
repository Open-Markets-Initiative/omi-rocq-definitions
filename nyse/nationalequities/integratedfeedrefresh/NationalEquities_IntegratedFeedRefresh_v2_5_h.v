From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Integrated Feed Refresh

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

Module NationalEquitiesIntegratedFeedRefreshV25H.

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
      late_close_eligible : N;
      eth_eligible : N;
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
      (late_close_eligible record < 256 ^ N.of_nat 1)%N /\
      (eth_eligible record < 256 ^ N.of_nat 1)%N.

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
      encode_uint 1 (late_close_eligible record) ++
      encode_uint 1 (eth_eligible record).

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
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (late_close_eligible_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (eth_eligible_value, bytes) =>
                                                                          Some ({| symbol_index := symbol_index_value; symbol := symbol_value; reserved_1 := reserved_1_value; market_id := market_id_value; system_id := system_id_value; exchange_code := exchange_code_value; price_scale_code := price_scale_code_value; security_type := security_type_value; lot_size := lot_size_value; prev_close_price := prev_close_price_value; prev_close_volume := prev_close_volume_value; price_resolution := price_resolution_value; round_lot := round_lot_value; mpv := mpv_value; unit_of_trade := unit_of_trade_value; late_close_eligible := late_close_eligible_value; eth_eligible := eth_eligible_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolIndexMappingMessage.

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

  Module ImbalanceMessage.

    (** Imbalance messages are published once a second during auctions to update price and volume information. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      reference_price : N;
      paired_qty : N;
      total_imbalance_qty : N;
      market_imbalance_qty : N;
      auction_time : N;
      auction_type : list byte;
      imbalance_side : list byte;
      continuous_book_clearing_price : N;
      auction_interest_clearing_price : N;
      ssr_filing_price : N;
      indicative_match_price : N;
      upper_collar : N;
      lower_collar : N;
      auction_status : N;
      freeze_status : N;
      num_extensions : N;
      unpaired_qty : N;
      unpaired_side : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (reference_price record < 256 ^ N.of_nat 4)%N /\
      (paired_qty record < 256 ^ N.of_nat 4)%N /\
      (total_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (market_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (auction_time record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (imbalance_side record) = 1 /\
      (continuous_book_clearing_price record < 256 ^ N.of_nat 4)%N /\
      (auction_interest_clearing_price record < 256 ^ N.of_nat 4)%N /\
      (ssr_filing_price record < 256 ^ N.of_nat 4)%N /\
      (indicative_match_price record < 256 ^ N.of_nat 4)%N /\
      (upper_collar record < 256 ^ N.of_nat 4)%N /\
      (lower_collar record < 256 ^ N.of_nat 4)%N /\
      (auction_status record < 256 ^ N.of_nat 1)%N /\
      (freeze_status record < 256 ^ N.of_nat 1)%N /\
      (num_extensions record < 256 ^ N.of_nat 1)%N /\
      (unpaired_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (unpaired_side record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (reference_price record) ++
      encode_uint 4 (paired_qty record) ++
      encode_uint 4 (total_imbalance_qty record) ++
      encode_uint 4 (market_imbalance_qty record) ++
      encode_uint 2 (auction_time record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (imbalance_side record) ++
      encode_uint 4 (continuous_book_clearing_price record) ++
      encode_uint 4 (auction_interest_clearing_price record) ++
      encode_uint 4 (ssr_filing_price record) ++
      encode_uint 4 (indicative_match_price record) ++
      encode_uint 4 (upper_collar record) ++
      encode_uint 4 (lower_collar record) ++
      encode_uint 1 (auction_status record) ++
      encode_uint 1 (freeze_status record) ++
      encode_uint 1 (num_extensions record) ++
      encode_uint 4 (unpaired_qty record) ++
      encode_bytes 1 (unpaired_side record) ++
      encode_uint 1 (reserved_1 record).

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
                      | Some (reference_price_value, bytes) =>
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
                                      | Some (auction_time_value, bytes) =>
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
                                                          | Some (ssr_filing_price_value, bytes) =>
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
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (freeze_status_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (num_extensions_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (unpaired_qty_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (unpaired_side_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (reserved_1_value, bytes) =>
                                                                                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; reference_price := reference_price_value; paired_qty := paired_qty_value; total_imbalance_qty := total_imbalance_qty_value; market_imbalance_qty := market_imbalance_qty_value; auction_time := auction_time_value; auction_type := auction_type_value; imbalance_side := imbalance_side_value; continuous_book_clearing_price := continuous_book_clearing_price_value; auction_interest_clearing_price := auction_interest_clearing_price_value; ssr_filing_price := ssr_filing_price_value; indicative_match_price := indicative_match_price_value; upper_collar := upper_collar_value; lower_collar := lower_collar_value; auction_status := auction_status_value; freeze_status := freeze_status_value; num_extensions := num_extensions_value; unpaired_qty := unpaired_qty_value; unpaired_side := unpaired_side_value; reserved_1 := reserved_1_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ImbalanceMessage.

  Module AddOrderRefreshMessage.

    (** The Add Order Refresh message can be sent in either of two contexts: refresh response or symbol refresh. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      firm_id : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (firm_id record) = 5 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 5 (firm_id record) ++
      encode_uint 1 (reserved_1 record).

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
                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; firm_id := firm_id_value; reserved_1 := reserved_1_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderRefreshMessage.

End NationalEquitiesIntegratedFeedRefreshV25H.
