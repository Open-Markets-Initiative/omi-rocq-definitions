From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Integrated Feed

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

Module NyseEquitiesIntegratedFeedV21G.

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

    (** This message is sent at the start of every second during periods of active data publication. *)
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

    (** This message is published over the real-time data channels at system startup or in the context of a refresh sequence after a Matching Engine or XDP Publisher failover. It provides referential data for a single specified symbol. *)
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

  Module RetransmissionRequestMessage.

    (** Clients who have experienced a sequence number gap and need a retransmission of the missed messages should send a Retransmission Request message via TCP to the Request Controller. A Request Response message will be sent over the TCP connection back to the client, and if the request was valid, the requested message(s) will be re-published over the relevant Retransmission multicast channel. *)
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

  Module RequestResponseMessage.

    (** This message will be sent immediately via TCP/IP in response to the client’s request for retransmission, refresh or Symbol Mapping messages. *)
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

    (** Clients who have experienced a failure and need a refresh of the state of one or all symbols in a specific channel should send a Retransmission Request message via TCP to the Request Controller. A Request Response message will be sent over the TCP connection back to the client, and if the request was valid, the requested message(s) will be published over the relevant Refresh multicast channel. *)
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

  Module SymbolClearMessage.

    (** In case of a failure and recovery of a Matching Engine or an XDP Publisher, the publisher may send a full state refresh for every symbol affected. This kind of unrequested refresh is preceded by a Symbol Clear message. The client should react to receipt of a Symbol Clear message by clearing all state information for the specified symbol in anticipation of receiving a full state refresh. *)
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

  Module AddOrderMessage.

    (** An Add Order message is published when a new visible order has been received and added to the book. The Order ID is assigned by the matching engine and is good for today only. It is unique across all markets, except that for NYSE Tape A symbols, it is only unique per matching engine instance. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      firm_id : list byte;
      num_parity_splits : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (firm_id record) = 5 /\
      (num_parity_splits record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 5 (firm_id record) ++
      encode_uint 1 (num_parity_splits record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                                      | Some (num_parity_splits_value, bytes) =>
                                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; firm_id := firm_id_value; num_parity_splits := num_parity_splits_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module ModifyOrderMessage.

    (** A Modify Order message is sent when the price or volume of an order is changed due to an event other than a cancel-replace, or full or partial execution. The content of the price and volume fields represent the new values after modification. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      position_change : N;
      prev_price_parity_splits : N;
      new_price_parity_splits : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (position_change record < 256 ^ N.of_nat 1)%N /\
      (prev_price_parity_splits record < 256 ^ N.of_nat 1)%N /\
      (new_price_parity_splits record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (position_change record) ++
      encode_uint 1 (prev_price_parity_splits record) ++
      encode_uint 1 (new_price_parity_splits record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (position_change_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (prev_price_parity_splits_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (new_price_parity_splits_value, bytes) =>
                                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; position_change := position_change_value; prev_price_parity_splits := prev_price_parity_splits_value; new_price_parity_splits := new_price_parity_splits_value |}, bytes)
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

  End ModifyOrderMessage.

  Module ReplaceOrderMessage.

    (** A Replace Order message is published when a cancel/replace order is received and executed. The sitting order is replaced with a new one containing the same symbol, side and attribution, a new Order ID, and the price and size specified. The sitting order must be removed from the book and replaced with the new order. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      new_order_id : N;
      price : N;
      volume : N;
      prev_price_parity_splits : N;
      new_price_parity_splits : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (new_order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (prev_price_parity_splits record < 256 ^ N.of_nat 1)%N /\
      (new_price_parity_splits record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (new_order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (prev_price_parity_splits record) ++
      encode_uint 1 (new_price_parity_splits record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (new_order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (prev_price_parity_splits_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (new_price_parity_splits_value, bytes) =>
                                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; new_order_id := new_order_id_value; price := price_value; volume := volume_value; prev_price_parity_splits := prev_price_parity_splits_value; new_price_parity_splits := new_price_parity_splits_value |}, bytes)
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

  End ReplaceOrderMessage.

  Module DeleteOrderMessage.

    (** A Delete Order message is published when an order is taken off of the book for any reason except for full execution, in which case an Order Execution message is sent. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      num_parity_splits : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (num_parity_splits record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (num_parity_splits record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (num_parity_splits_value, bytes) =>
                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; num_parity_splits := num_parity_splits_value |}, bytes)
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

  End DeleteOrderMessage.

  Module TradeCancelMessage.

    (** In the event that an earlier trade has been reported in error, a Trade Cancel message is sent. This occurs whether the initial report was an Order Execution or a Non-Displayed Trade message. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                      Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value |}, bytes)
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

  End TradeCancelMessage.

  Module CrossTradeMessage.

    (** A Cross Trade message is published on completion of a crossing auction, and shows the bulk volume that traded in the auction. The Reason Code field indicates the auction type. Additionally, a non-printable Order Execution or Trade message will be published for each order that traded. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      cross_id : N;
      price : N;
      volume : N;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
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
          | Some (symbol_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_seq_num_value, bytes) =>
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
                                  Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; cross_id := cross_id_value; price := price_value; volume := volume_value; cross_type := cross_type_value |}, bytes)
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

  End CrossTradeMessage.

  Module CrossCorrectionMessage.

    (** In the event that an earlier Cross Trade has been reported in error, a Cross Correction message is sent. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      cross_id : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                  | Some (cross_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; cross_id := cross_id_value; volume := volume_value |}, bytes)
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

  End CrossCorrectionMessage.

  Module RetailPriceImprovementMessage.

    (** Published when RPI interest (hidden retail price improvement interest) is added or removed between the best bid and best offer price. When all RPI interest for this security is removed from the book, An RPI message with RPIIndicator = ' ' (space character) is published. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      rpi_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (rpi_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (rpi_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                  | Some (rpi_indicator_value, bytes) =>
                      Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; rpi_indicator := rpi_indicator_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetailPriceImprovementMessage.

  Module AddOrderRefreshMessage.

    (** The Add Order Refresh message can be sent in either of two contexts: 1) If a client sends a Refresh Request to the Request Controller, an Add Order Refresh message is sent over the Refresh channels as part of the refresh response for every order currently sitting on the book. 2) If NYSE Operations refreshes a symbol, a Symbol Clear message is published, followed by a full refresh. The refresh includes an Add Order Refresh message for every order currently sitting on the book of the symbol. *)
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
      num_parity_splits : N;
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
      (num_parity_splits record < 256 ^ N.of_nat 1)%N.

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
      encode_uint 1 (num_parity_splits record).

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
                                          | Some (num_parity_splits_value, bytes) =>
                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; firm_id := firm_id_value; num_parity_splits := num_parity_splits_value |}, bytes)
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

  Module ImbalanceMessage.

    (** Imbalance messages are sent periodically during auctions to update price and volume information. If there is no change to the calculated fields, no message will be generated. *)
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
      closing_only_clearing_price : N;
      ssr_filing_price : N;
      indicative_match_price : N;
      upper_collar : N;
      lower_collar : N;
      auction_status : N;
      freeze_status : N;
      num_extensions : N;
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
      (closing_only_clearing_price record < 256 ^ N.of_nat 4)%N /\
      (ssr_filing_price record < 256 ^ N.of_nat 4)%N /\
      (indicative_match_price record < 256 ^ N.of_nat 4)%N /\
      (upper_collar record < 256 ^ N.of_nat 4)%N /\
      (lower_collar record < 256 ^ N.of_nat 4)%N /\
      (auction_status record < 256 ^ N.of_nat 1)%N /\
      (freeze_status record < 256 ^ N.of_nat 1)%N /\
      (num_extensions record < 256 ^ N.of_nat 1)%N.

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
      encode_uint 4 (closing_only_clearing_price record) ++
      encode_uint 4 (ssr_filing_price record) ++
      encode_uint 4 (indicative_match_price record) ++
      encode_uint 4 (upper_collar record) ++
      encode_uint 4 (lower_collar record) ++
      encode_uint 1 (auction_status record) ++
      encode_uint 1 (freeze_status record) ++
      encode_uint 1 (num_extensions record).

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
                                                      | Some (closing_only_clearing_price_value, bytes) =>
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
                                                                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; reference_price := reference_price_value; paired_qty := paired_qty_value; total_imbalance_qty := total_imbalance_qty_value; market_imbalance_qty := market_imbalance_qty_value; auction_time := auction_time_value; auction_type := auction_type_value; imbalance_side := imbalance_side_value; continuous_book_clearing_price := continuous_book_clearing_price_value; closing_only_clearing_price := closing_only_clearing_price_value; ssr_filing_price := ssr_filing_price_value; indicative_match_price := indicative_match_price_value; upper_collar := upper_collar_value; lower_collar := lower_collar_value; auction_status := auction_status_value; freeze_status := freeze_status_value; num_extensions := num_extensions_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ImbalanceMessage.

  Module OrderExecutionMessage.

    (** An Order Execution message is sent when an order is partially or fully executed. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      trade_id : N;
      price : N;
      volume : N;
      printable_flag : N;
      num_parity_splits : N;
      db_exec_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (printable_flag record < 256 ^ N.of_nat 1)%N /\
      (num_parity_splits record < 256 ^ N.of_nat 1)%N /\
      (db_exec_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (printable_flag record) ++
      encode_uint 1 (num_parity_splits record) ++
      encode_uint 4 (db_exec_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                                      | Some (num_parity_splits_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (db_exec_id_value, bytes) =>
                                              Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; trade_id := trade_id_value; price := price_value; volume := volume_value; printable_flag := printable_flag_value; num_parity_splits := num_parity_splits_value; db_exec_id := db_exec_id_value |}, bytes)
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

  End OrderExecutionMessage.

  Module NonDisplayedTradeMessage.

    (** An Non Displayed Trade message is sent as a result of a match between two non-displayed orders. *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      volume : N;
      printable_flag : N;
      db_exec_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (printable_flag record < 256 ^ N.of_nat 1)%N /\
      (db_exec_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (printable_flag record) ++
      encode_uint 4 (db_exec_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (printable_flag_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (db_exec_id_value, bytes) =>
                                      Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; volume := volume_value; printable_flag := printable_flag_value; db_exec_id := db_exec_id_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End NonDisplayedTradeMessage.

  Module StockSummaryMessage.

    (** On a separate channel from the main feed, the Stock Summary channel, a Stock Summary message per symbol is sent every 60 seconds. The message is sent regardless of whether there has been a change to the symbol in the last 60 seconds or not. *)
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

End NyseEquitiesIntegratedFeedV21G.
