From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Order Entry

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
      - the dispatch that chooses a message by its type
      - a Composite rule
      - a field read in bits
      - a length prefix framing what follows

    License: MIT No Attribution
  *)

Module NseSlbmOrderEntryV27Server.

  Module PacketHeader.

    (** Direct interface twenty two byte packet header *)
    Record t := {
      packet_length : N;
      packet_sequence_number : N;
      checksum : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (checksum record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_uint 4 (packet_sequence_number record) ++
      encode_bytes 16 (checksum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (packet_sequence_number_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (checksum_value, bytes) =>
                  Some ({| packet_length := packet_length_value; packet_sequence_number := packet_sequence_number_value; checksum := checksum_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End PacketHeader.

  Module MessageHeader.

    (** MESSAGE_HEADER *)
    Record t := {
      transaction_code : N;
      log_time : N;
      alpha_char : list byte;
      trader_id : N;
      error_code : N;
      header_timestamp : N;
      time_stamp_1 : list byte;
      time_stamp_2 : list byte;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_code record < 256 ^ N.of_nat 2)%N /\
      (log_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (alpha_char record) = 2 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (header_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (time_stamp_1 record) = 8 /\
      Datatypes.length (time_stamp_2 record) = 8 /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (transaction_code record) ++
      encode_uint 4 (log_time record) ++
      encode_bytes 2 (alpha_char record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (error_code record) ++
      encode_uint 8 (header_timestamp record) ++
      encode_bytes 8 (time_stamp_1 record) ++
      encode_bytes 8 (time_stamp_2 record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (transaction_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (log_time_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (alpha_char_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trader_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (error_code_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (header_timestamp_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (time_stamp_1_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (time_stamp_2_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (message_length_value, bytes) =>
                                          Some ({| transaction_code := transaction_code_value; log_time := log_time_value; alpha_char := alpha_char_value; trader_id := trader_id_value; error_code := error_code_value; header_timestamp := header_timestamp_value; time_stamp_1 := time_stamp_1_value; time_stamp_2 := time_stamp_2_value; message_length := message_length_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
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

  End MessageHeader.

  Module SecInfo.

    (** SEC_INFO *)
    Record t := {
      symbol : list byte;
      series : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 10 /\
      Datatypes.length (series record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (symbol record) ++
      encode_bytes 2 (series record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (series_value, bytes) =>
              Some ({| symbol := symbol_value; series := series_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End SecInfo.

  Module LogonErrorBody.

    (** Logon Error Body *)
    Record t := {
      sec_info : SecInfo.t;
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo.bounded (sec_info record) /\
      Datatypes.length (error_message record) = 128.

    Definition encode (record : t) : list byte :=
      SecInfo.encode (sec_info record) ++
      encode_bytes 128 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_bytes 128 bytes with
          | None => None
          | Some (error_message_value, bytes) =>
              Some ({| sec_info := sec_info_value; error_message := error_message_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 140.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo.eq_dec]. Defined.

  End LogonErrorBody.

  Module UpdateLocalDatabaseHeaderMessage.

    (** Sent as UPDATE_LOCALDB_HEADER to signal that the local database download is starting *)
    Record t := {
      reserved_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          Some ({| reserved_2 := reserved_2_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End UpdateLocalDatabaseHeaderMessage.

  Module UpdateLocalDatabaseTrailerMessage.

    (** Sent as UPDATE_LOCALDB_TRAILER to signal that the local database download is complete *)
    Record t := {
      reserved_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          Some ({| reserved_2 := reserved_2_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End UpdateLocalDatabaseTrailerMessage.

  Module TradeCancellationRequestedResponseMessage.

    (** Sent as TRADE_CANCEL_OUT to acknowledge that the request reached the trading system *)
    Record t := {
      sec_info : SecInfo.t;
      reverse_leg_settl_date : N;
      l_fill_number : N;
      l_fill_qty : N;
      l_fill_price : N;
      i_mkt_type : N;
      l_new_volume : N;
      buy_participant_id : list byte;
      sell_participant_id : list byte;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo.bounded (sec_info record) /\
      (reverse_leg_settl_date record < 256 ^ N.of_nat 4)%N /\
      (l_fill_number record < 256 ^ N.of_nat 4)%N /\
      (l_fill_qty record < 256 ^ N.of_nat 4)%N /\
      (l_fill_price record < 256 ^ N.of_nat 4)%N /\
      (i_mkt_type record < 256 ^ N.of_nat 2)%N /\
      (l_new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_participant_id record) = 12 /\
      Datatypes.length (sell_participant_id record) = 12 /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (requested_by record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      SecInfo.encode (sec_info record) ++
      encode_uint 4 (reverse_leg_settl_date record) ++
      encode_uint 4 (l_fill_number record) ++
      encode_uint 4 (l_fill_qty record) ++
      encode_uint 4 (l_fill_price record) ++
      encode_uint 2 (i_mkt_type record) ++
      encode_uint 4 (l_new_volume record) ++
      encode_bytes 12 (buy_participant_id record) ++
      encode_bytes 12 (sell_participant_id record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (requested_by record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reverse_leg_settl_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (l_fill_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (l_fill_qty_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (l_fill_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (i_mkt_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (l_new_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (buy_participant_id_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (sell_participant_id_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (buy_broker_id_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (sell_broker_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (trader_id_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (requested_by_value, bytes) =>
                                                          Some ({| sec_info := sec_info_value; reverse_leg_settl_date := reverse_leg_settl_date_value; l_fill_number := l_fill_number_value; l_fill_qty := l_fill_qty_value; l_fill_price := l_fill_price_value; i_mkt_type := i_mkt_type_value; l_new_volume := l_new_volume_value; buy_participant_id := buy_participant_id_value; sell_participant_id := sell_participant_id_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo.decode_encode by exact bound_0.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo.eq_dec]. Defined.

  End TradeCancellationRequestedResponseMessage.

  Module TradeCancellationErrorMessage.

    (** Sent as TRADE_ERROR when an error is detected in the request *)
    Record t := {
      sec_info : SecInfo.t;
      reverse_leg_settl_date : N;
      l_fill_number : N;
      l_fill_qty : N;
      l_fill_price : N;
      i_mkt_type : N;
      l_new_volume : N;
      buy_participant_id : list byte;
      sell_participant_id : list byte;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo.bounded (sec_info record) /\
      (reverse_leg_settl_date record < 256 ^ N.of_nat 4)%N /\
      (l_fill_number record < 256 ^ N.of_nat 4)%N /\
      (l_fill_qty record < 256 ^ N.of_nat 4)%N /\
      (l_fill_price record < 256 ^ N.of_nat 4)%N /\
      (i_mkt_type record < 256 ^ N.of_nat 2)%N /\
      (l_new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_participant_id record) = 12 /\
      Datatypes.length (sell_participant_id record) = 12 /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (requested_by record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      SecInfo.encode (sec_info record) ++
      encode_uint 4 (reverse_leg_settl_date record) ++
      encode_uint 4 (l_fill_number record) ++
      encode_uint 4 (l_fill_qty record) ++
      encode_uint 4 (l_fill_price record) ++
      encode_uint 2 (i_mkt_type record) ++
      encode_uint 4 (l_new_volume record) ++
      encode_bytes 12 (buy_participant_id record) ++
      encode_bytes 12 (sell_participant_id record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (requested_by record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reverse_leg_settl_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (l_fill_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (l_fill_qty_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (l_fill_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (i_mkt_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (l_new_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (buy_participant_id_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (sell_participant_id_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (buy_broker_id_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (sell_broker_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (trader_id_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (requested_by_value, bytes) =>
                                                          Some ({| sec_info := sec_info_value; reverse_leg_settl_date := reverse_leg_settl_date_value; l_fill_number := l_fill_number_value; l_fill_qty := l_fill_qty_value; l_fill_price := l_fill_price_value; i_mkt_type := i_mkt_type_value; l_new_volume := l_new_volume_value; buy_participant_id := buy_participant_id_value; sell_participant_id := sell_participant_id_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo.decode_encode by exact bound_0.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo.eq_dec]. Defined.

  End TradeCancellationErrorMessage.

  Module TradeModificationRequestedResponseMessage.

    (** Sent as TRADE_MOD_OUT; trade modification is currently not allowed *)
    Record t := {
      sec_info : SecInfo.t;
      reverse_leg_settl_date : N;
      l_fill_number : N;
      l_fill_qty : N;
      l_fill_price : N;
      i_mkt_type : N;
      l_new_volume : N;
      buy_participant_id : list byte;
      sell_participant_id : list byte;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo.bounded (sec_info record) /\
      (reverse_leg_settl_date record < 256 ^ N.of_nat 4)%N /\
      (l_fill_number record < 256 ^ N.of_nat 4)%N /\
      (l_fill_qty record < 256 ^ N.of_nat 4)%N /\
      (l_fill_price record < 256 ^ N.of_nat 4)%N /\
      (i_mkt_type record < 256 ^ N.of_nat 2)%N /\
      (l_new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_participant_id record) = 12 /\
      Datatypes.length (sell_participant_id record) = 12 /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (requested_by record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      SecInfo.encode (sec_info record) ++
      encode_uint 4 (reverse_leg_settl_date record) ++
      encode_uint 4 (l_fill_number record) ++
      encode_uint 4 (l_fill_qty record) ++
      encode_uint 4 (l_fill_price record) ++
      encode_uint 2 (i_mkt_type record) ++
      encode_uint 4 (l_new_volume record) ++
      encode_bytes 12 (buy_participant_id record) ++
      encode_bytes 12 (sell_participant_id record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 2 (requested_by record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reverse_leg_settl_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (l_fill_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (l_fill_qty_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (l_fill_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (i_mkt_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (l_new_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (buy_participant_id_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (sell_participant_id_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (buy_broker_id_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (sell_broker_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (trader_id_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (requested_by_value, bytes) =>
                                                          Some ({| sec_info := sec_info_value; reverse_leg_settl_date := reverse_leg_settl_date_value; l_fill_number := l_fill_number_value; l_fill_qty := l_fill_qty_value; l_fill_price := l_fill_price_value; i_mkt_type := i_mkt_type_value; l_new_volume := l_new_volume_value; buy_participant_id := buy_participant_id_value; sell_participant_id := sell_participant_id_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo.decode_encode by exact bound_0.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo.eq_dec]. Defined.

  End TradeModificationRequestedResponseMessage.

  Module ControlMessageToTraderMessage.

    (** Sent as CTRL_MSG_TO_TRADER for a message from NSE-Control to a particular user, and for a counter party's trade cancellation request *)
    Record t := {
      trader_id : N;
      action_code : list byte;
      reserved_1 : list byte;
      msg_length : N;
      msg : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (action_code record) = 3 /\
      Datatypes.length (reserved_1 record) = 1 /\
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg record) = 239.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trader_id record) ++
      encode_bytes 3 (action_code record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_uint 2 (msg_length record) ++
      encode_bytes 239 (msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (action_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (msg_length_value, bytes) =>
                      match decode_bytes 239 bytes with
                      | None => None
                      | Some (msg_value, bytes) =>
                          Some ({| trader_id := trader_id_value; action_code := action_code_value; reserved_1 := reserved_1_value; msg_length := msg_length_value; msg := msg_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 249.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ControlMessageToTraderMessage.

  Module ErrorResponseMessage.

    (** Sent as ERROR_RESPONSE_OUT when the Error Code of the header is not zero *)
    Record t := {
      sec_info : SecInfo.t;
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SecInfo.bounded (sec_info record) /\
      Datatypes.length (error_message record) = 128.

    Definition encode (record : t) : list byte :=
      SecInfo.encode (sec_info record) ++
      encode_bytes 128 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SecInfo.decode bytes with
      | None => None
      | Some (sec_info_value, bytes) =>
          match decode_bytes 128 bytes with
          | None => None
          | Some (error_message_value, bytes) =>
              Some ({| sec_info := sec_info_value; error_message := error_message_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 140.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SecInfo.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SecInfo.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SecInfo.eq_dec]. Defined.

  End ErrorResponseMessage.

  Module GatewayRouterResponseMessage.

    (** Sent as GR_RESPONSE with the allocated gateway server, its session key and the cryptographic key and vector *)
    Record t := {
      box_id : N;
      broker_id : list byte;
      filler : list byte;
      ip_address : list byte;
      port : N;
      session_key : list byte;
      cryptographic_key : list byte;
      cryptographic_iv_initialization_vector : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_id record) = 5 /\
      Datatypes.length (filler record) = 1 /\
      Datatypes.length (ip_address record) = 16 /\
      (port record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (session_key record) = 8 /\
      Datatypes.length (cryptographic_key record) = 32 /\
      Datatypes.length (cryptographic_iv_initialization_vector record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 5 (broker_id record) ++
      encode_bytes 1 (filler record) ++
      encode_bytes 16 (ip_address record) ++
      encode_uint 4 (port record) ++
      encode_bytes 8 (session_key record) ++
      encode_bytes 32 (cryptographic_key record) ++
      encode_bytes 16 (cryptographic_iv_initialization_vector record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (broker_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (ip_address_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (port_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (session_key_value, bytes) =>
                              match decode_bytes 32 bytes with
                              | None => None
                              | Some (cryptographic_key_value, bytes) =>
                                  match decode_bytes 16 bytes with
                                  | None => None
                                  | Some (cryptographic_iv_initialization_vector_value, bytes) =>
                                      Some ({| box_id := box_id_value; broker_id := broker_id_value; filler := filler_value; ip_address := ip_address_value; port := port_value; session_key := session_key_value; cryptographic_key := cryptographic_key_value; cryptographic_iv_initialization_vector := cryptographic_iv_initialization_vector_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GatewayRouterResponseMessage.

  Module BoxSignOnResponseMessage.

    (** Sent as BOX_SIGN_ON_REQUEST_OUT; an error terminates the box connection *)
    Record t := {
      box_id : N;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (reserved_10_value, bytes) =>
              Some ({| box_id := box_id_value; reserved_10 := reserved_10_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BoxSignOnResponseMessage.

  Module BoxSignOffMessage.

    (** Sent as BOX_SIGN_OFF with an error code when the exchange terminates the connection *)
    Record t := {
      box_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          Some ({| box_id := box_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End BoxSignOffMessage.

End NseSlbmOrderEntryV27Server.
