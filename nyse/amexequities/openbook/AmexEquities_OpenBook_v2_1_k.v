From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Open Book

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
      - a length prefix framing what follows
      - a run counted by a field
      - a run filling what frames it
  *)

Module AmexEquitiesOpenBookV21K.

  Module PacketHeader.

    (** OpenBook Ultra packet header *)
    Record t := {
      packet_size : N;
      message_type : N;
      sequence_number : N;
      timestamp : N;
      product_id : N;
      retransmission_flag : N;
      message_count : N;
      link_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (retransmission_flag record < 256 ^ N.of_nat 1)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (link_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_size record) ++
      encode_uint 2 (message_type record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (timestamp record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (retransmission_flag record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (link_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (sequence_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (timestamp_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (product_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (retransmission_flag_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (message_count_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (link_flag_value, bytes) =>
                                      Some ({| packet_size := packet_size_value; message_type := message_type_value; sequence_number := sequence_number_value; timestamp := timestamp_value; product_id := product_id_value; retransmission_flag := retransmission_flag_value; message_count := message_count_value; link_flag := link_flag_value |}, bytes)
                                  end
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

  End PacketHeader.

  Module SequenceNumberResetMessage.

    (** This message is sent to reset the Packet Sequence Number. *)
    Record t := {
      next_seq_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_seq_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (next_seq_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (next_seq_number_value, bytes) =>
          Some ({| next_seq_number := next_seq_number_value |}, bytes)
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

  End SequenceNumberResetMessage.

  Module UnavailableMessage.

    (** This message will be sent over the Retransmission multicast channels to inform the clients of unavailability of a range of messages for which they have requested a retransmission. *)
    Record t := {
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_seq_num_value, bytes) =>
              Some ({| begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End UnavailableMessage.

  Module RequestResponseMessage.

    (** This message will be sent immediately via TCP/IP in response to the client's request for a retransmission, refresh, or Symbol Index information. *)
    Record t := {
      source_seq_num : N;
      source_id : list byte;
      status : list byte;
      reject_reason : list byte;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (source_id record) = 20 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reject_reason record) = 1 /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_seq_num record) ++
      encode_bytes 20 (source_id record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (reject_reason record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_seq_num_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (source_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reject_reason_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (filler_2_value, bytes) =>
                          Some ({| source_seq_num := source_seq_num_value; source_id := source_id_value; status := status_value; reject_reason := reject_reason_value; filler_2 := filler_2_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RequestResponseMessage.

  Module RetransmissionRequestMessage.

    (** This message is sent by clients to request a retransmission of missed packets. *)
    Record t := {
      begin_seq_num : N;
      end_seq_num : N;
      source_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (source_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record) ++
      encode_bytes 20 (source_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_num_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_seq_num_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (source_id_value, bytes) =>
                  Some ({| begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value; source_id := source_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmissionRequestMessage.

  Module BookRefreshRequestMessage.

    (** This message is sent by clients requesting a full book refresh. *)
    Record t := {
      symbol_16 : list byte;
      source_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_16 record) = 16 /\
      Datatypes.length (source_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (symbol_16 record) ++
      encode_bytes 20 (source_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (symbol_16_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (source_id_value, bytes) =>
              Some ({| symbol_16 := symbol_16_value; source_id := source_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End BookRefreshRequestMessage.

  Module HeartbeatResponseMessage.

    (** Clients that remain connected to the Request server intraday must respond within 120 seconds to any heartbeat received with a single message of this type in its own packet. *)
    Record t := {
      source_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (source_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (source_id_value, bytes) =>
          Some ({| source_id := source_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  Module ExtendedBookRefreshRequestMessage.

    (** The Extended Book Refresh Request message allows the client to request a refresh by symbol index as opposed to symbol, and to request a refresh of all symbols in a channel. *)
    Record t := {
      source_id : list byte;
      symbol_index : N;
      msg_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source_id record) = 20 /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (msg_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (source_id record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 2 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (source_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_index_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (msg_type_value, bytes) =>
                  Some ({| source_id := source_id_value; symbol_index := symbol_index_value; msg_type := msg_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExtendedBookRefreshRequestMessage.

  Module SymbolIndexMappingRequestMessage.

    (** This message is sent by clients requesting a refresh of Symbol Index mapping information only. *)
    Record t := {
      source_id : list byte;
      symbol_index : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source_id record) = 20 /\
      (symbol_index record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (source_id record) ++
      encode_uint 4 (symbol_index record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (source_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_index_value, bytes) =>
              Some ({| source_id := source_id_value; symbol_index := symbol_index_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End SymbolIndexMappingRequestMessage.

End AmexEquitiesOpenBookV21K.
