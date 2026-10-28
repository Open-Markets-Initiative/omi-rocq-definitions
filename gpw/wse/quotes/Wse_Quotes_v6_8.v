From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Quotes

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

Module WseQuotesV68.

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

  Module QuotesAndBbo5Message.

    (** A Quotes & BBO5 message indicates the modification of one or more of the N best limits (N being the number of limits disseminated for the given exchange 1 ) for an instrument and, during the Pre-Opening phase, the modification of the "market summary" for the instrument *)
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
      reserved_1 : N;
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
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

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
                                                                          | Some (reserved_1_value, bytes) =>
                                                                              Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; quote_link_id := quote_link_id_value; ask_price := ask_price_value; ask_size := ask_size_value; bid_price := bid_price_value; bid_size := bid_size_value; system_id := system_id_value; number_ask_orders := number_ask_orders_value; number_bid_orders := number_bid_orders_value; source_time_micro_secs := source_time_micro_secs_value; type_of_ask_price := type_of_ask_price_value; type_of_bid_price := type_of_bid_price_value; quote_condition := quote_condition_value; quote_number := quote_number_value; price_scale_code := price_scale_code_value; reserved_1 := reserved_1_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

  End QuotesAndBbo5Message.

  Module IndicationOfInterestMessage.

    (** The Indication of Interest message disseminates an indication of interest for a given instrument to all participants *)
    Record t := {
      symbol_index : N;
      source_seq_num : N;
      source_time : N;
      ioiutpid : N;
      ioi_qty : N;
      price : N;
      validity_time : N;
      system_id : N;
      source_time_micro_secs : N;
      price_scale_code : N;
      ioi_trans_type : list byte;
      firm_id : list byte;
      side : list byte;
      settlement_date : list byte;
      text : list byte;
      trade_type : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (ioiutpid record < 256 ^ N.of_nat 4)%N /\
      (ioi_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (validity_time record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (ioi_trans_type record) = 1 /\
      Datatypes.length (firm_id record) = 11 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (settlement_date record) = 8 /\
      Datatypes.length (text record) = 100 /\
      Datatypes.length (trade_type record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (ioiutpid record) ++
      encode_uint 4 (ioi_qty record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (validity_time record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 1 (ioi_trans_type record) ++
      encode_bytes 11 (firm_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 8 (settlement_date record) ++
      encode_bytes 100 (text record) ++
      encode_bytes 1 (trade_type record) ++
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
                  | Some (ioiutpid_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ioi_qty_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (validity_time_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (system_id_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (source_time_micro_secs_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (price_scale_code_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (ioi_trans_type_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (firm_id_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (settlement_date_value, bytes) =>
                                                              match decode_bytes 100 bytes with
                                                              | None => None
                                                              | Some (text_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_type_value, bytes) =>
                                                                      match decode_uint 3 bytes with
                                                                      | None => None
                                                                      | Some (reserved_3_value, bytes) =>
                                                                          Some ({| symbol_index := symbol_index_value; source_seq_num := source_seq_num_value; source_time := source_time_value; ioiutpid := ioiutpid_value; ioi_qty := ioi_qty_value; price := price_value; validity_time := validity_time_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; price_scale_code := price_scale_code_value; ioi_trans_type := ioi_trans_type_value; firm_id := firm_id_value; side := side_value; settlement_date := settlement_date_value; text := text_value; trade_type := trade_type_value; reserved_3 := reserved_3_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 160.
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
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicationOfInterestMessage.

End WseQuotesV68.
