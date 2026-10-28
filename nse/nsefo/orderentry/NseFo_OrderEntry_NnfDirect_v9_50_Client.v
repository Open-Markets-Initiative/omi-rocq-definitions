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
      - a Composite rule
      - a field read in bits
      - a run counted by a field
  *)

Module NseFoOrderEntryV950Client.

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

  Module SystemInformationInMessage.

    (** Requests the system information of the trading system *)
    Record t := {
      last_update_portfolio_t_ime : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_portfolio_t_ime record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_update_portfolio_t_ime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_update_portfolio_t_ime_value, bytes) =>
          Some ({| last_update_portfolio_t_ime := last_update_portfolio_t_ime_value |}, bytes)
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

  End SystemInformationInMessage.

  Module GatewayRouterRequestMessage.

    (** Asks the gateway router which gateway server to connect to *)
    Record t := {
      box_id : N;
      broker_id : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_id record) = 5 /\
      Datatypes.length (filler record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 5 (broker_id record) ++
      encode_bytes 1 (filler record).

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
                  Some ({| box_id := box_id_value; broker_id := broker_id_value; filler := filler_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GatewayRouterRequestMessage.

  Module StMarketStatus.

    (** ST_MARKET_STATUS *)
    Record t := {
      market_status_normal : N;
      market_status_oddlot : N;
      market_status_spot : N;
      market_status_auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_status_normal record < 256 ^ N.of_nat 2)%N /\
      (market_status_oddlot record < 256 ^ N.of_nat 2)%N /\
      (market_status_spot record < 256 ^ N.of_nat 2)%N /\
      (market_status_auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (market_status_normal record) ++
      encode_uint 2 (market_status_oddlot record) ++
      encode_uint 2 (market_status_spot record) ++
      encode_uint 2 (market_status_auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (market_status_normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (market_status_oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (market_status_spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_status_auction_value, bytes) =>
                      Some ({| market_status_normal := market_status_normal_value; market_status_oddlot := market_status_oddlot_value; market_status_spot := market_status_spot_value; market_status_auction := market_status_auction_value |}, bytes)
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

  End StMarketStatus.

  Module StExMarketStatus.

    (** ST_EX_MARKET_STATUS *)
    Record t := {
      ex_market_status_normal : N;
      ex_market_status_oddlot : N;
      ex_market_status_spot : N;
      ex_market_status_auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ex_market_status_normal record < 256 ^ N.of_nat 2)%N /\
      (ex_market_status_oddlot record < 256 ^ N.of_nat 2)%N /\
      (ex_market_status_spot record < 256 ^ N.of_nat 2)%N /\
      (ex_market_status_auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (ex_market_status_normal record) ++
      encode_uint 2 (ex_market_status_oddlot record) ++
      encode_uint 2 (ex_market_status_spot record) ++
      encode_uint 2 (ex_market_status_auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (ex_market_status_normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (ex_market_status_oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (ex_market_status_spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (ex_market_status_auction_value, bytes) =>
                      Some ({| ex_market_status_normal := ex_market_status_normal_value; ex_market_status_oddlot := ex_market_status_oddlot_value; ex_market_status_spot := ex_market_status_spot_value; ex_market_status_auction := ex_market_status_auction_value |}, bytes)
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

  End StExMarketStatus.

  Module StPlMarketStatus.

    (** ST_PL_MARKET_STATUS *)
    Record t := {
      pl_market_status_normal : N;
      pl_market_status_oddlot : N;
      pl_market_status_spot : N;
      pl_market_status_auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pl_market_status_normal record < 256 ^ N.of_nat 2)%N /\
      (pl_market_status_oddlot record < 256 ^ N.of_nat 2)%N /\
      (pl_market_status_spot record < 256 ^ N.of_nat 2)%N /\
      (pl_market_status_auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (pl_market_status_normal record) ++
      encode_uint 2 (pl_market_status_oddlot record) ++
      encode_uint 2 (pl_market_status_spot record) ++
      encode_uint 2 (pl_market_status_auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (pl_market_status_normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (pl_market_status_oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (pl_market_status_spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (pl_market_status_auction_value, bytes) =>
                      Some ({| pl_market_status_normal := pl_market_status_normal_value; pl_market_status_oddlot := pl_market_status_oddlot_value; pl_market_status_spot := pl_market_status_spot_value; pl_market_status_auction := pl_market_status_auction_value |}, bytes)
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

  End StPlMarketStatus.

  Module UpdateLocalDatabaseInMessage.

    (** Requests the local database download of contracts and participants *)
    Record t := {
      last_update_security_time : N;
      last_update_participant_time : N;
      last_update_instrument_time : N;
      last_update_index_time : N;
      request_for_open_orders : list byte;
      reserved_1 : N;
      st_market_status : StMarketStatus.t;
      st_ex_market_status : StExMarketStatus.t;
      st_pl_market_status : StPlMarketStatus.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_security_time record < 256 ^ N.of_nat 4)%N /\
      (last_update_participant_time record < 256 ^ N.of_nat 4)%N /\
      (last_update_instrument_time record < 256 ^ N.of_nat 4)%N /\
      (last_update_index_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (request_for_open_orders record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      StMarketStatus.bounded (st_market_status record) /\
      StExMarketStatus.bounded (st_ex_market_status record) /\
      StPlMarketStatus.bounded (st_pl_market_status record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_update_security_time record) ++
      encode_uint 4 (last_update_participant_time record) ++
      encode_uint 4 (last_update_instrument_time record) ++
      encode_uint 4 (last_update_index_time record) ++
      encode_bytes 1 (request_for_open_orders record) ++
      encode_uint 1 (reserved_1 record) ++
      StMarketStatus.encode (st_market_status record) ++
      StExMarketStatus.encode (st_ex_market_status record) ++
      StPlMarketStatus.encode (st_pl_market_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_update_security_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (last_update_participant_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (last_update_instrument_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (last_update_index_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (request_for_open_orders_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              match StMarketStatus.decode bytes with
                              | None => None
                              | Some (st_market_status_value, bytes) =>
                                  match StExMarketStatus.decode bytes with
                                  | None => None
                                  | Some (st_ex_market_status_value, bytes) =>
                                      match StPlMarketStatus.decode bytes with
                                      | None => None
                                      | Some (st_pl_market_status_value, bytes) =>
                                          Some ({| last_update_security_time := last_update_security_time_value; last_update_participant_time := last_update_participant_time_value; last_update_instrument_time := last_update_instrument_time_value; last_update_index_time := last_update_index_time_value; request_for_open_orders := request_for_open_orders_value; reserved_1 := reserved_1_value; st_market_status := st_market_status_value; st_ex_market_status := st_ex_market_status_value; st_pl_market_status := st_pl_market_status_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !StMarketStatus.encode_length, !StExMarketStatus.encode_length, !StPlMarketStatus.encode_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite StMarketStatus.decode_encode by exact bound_6.
      rewrite StExMarketStatus.decode_encode by exact bound_7.
      rewrite StPlMarketStatus.decode_encode by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply StMarketStatus.eq_dec | apply StExMarketStatus.eq_dec | apply StPlMarketStatus.eq_dec]. Defined.

  End UpdateLocalDatabaseInMessage.

  Module ContractDesc.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc.

  Module ContractDesc2.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc2.

  Module ContractDesc3.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc3.

  Module ContractDesc4.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc4.

  Module ContractDesc5.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc5.

  Module ContractDesc6.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc6.

  Module ContractDesc7.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc7.

  Module TradeInquiryMessage.

    (** Trade modification and cancellation requests, the cancellation response and the trade error, all carried in the shared trade structure. Transaction Code in the header names the operation *)
    Record t := {
      token_no : N;
      contract_desc : ContractDesc7.t;
      fill_number : N;
      fill_quantity : N;
      fill_price : N;
      mkt_type : list byte;
      buy_open_close : list byte;
      reserved_4 : N;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : list byte;
      sell_open_close : list byte;
      buy_account_number : list byte;
      sell_account_number : list byte;
      reserved_24 : list byte;
      reserved_2 : N;
      second_reserved_2 : N;
      buy_pan : list byte;
      sell_pan : list byte;
      reserved_60 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (token_no record < 256 ^ N.of_nat 4)%N /\
      ContractDesc7.bounded (contract_desc record) /\
      (fill_number record < 256 ^ N.of_nat 4)%N /\
      (fill_quantity record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mkt_type record) = 1 /\
      Datatypes.length (buy_open_close record) = 1 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (requested_by record) = 1 /\
      Datatypes.length (sell_open_close record) = 1 /\
      Datatypes.length (buy_account_number record) = 10 /\
      Datatypes.length (sell_account_number record) = 10 /\
      Datatypes.length (reserved_24 record) = 24 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (second_reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (buy_pan record) = 10 /\
      Datatypes.length (sell_pan record) = 10 /\
      Datatypes.length (reserved_60 record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (token_no record) ++
      ContractDesc7.encode (contract_desc record) ++
      encode_uint 4 (fill_number record) ++
      encode_uint 4 (fill_quantity record) ++
      encode_uint 4 (fill_price record) ++
      encode_bytes 1 (mkt_type record) ++
      encode_bytes 1 (buy_open_close record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_bytes 1 (requested_by record) ++
      encode_bytes 1 (sell_open_close record) ++
      encode_bytes 10 (buy_account_number record) ++
      encode_bytes 10 (sell_account_number record) ++
      encode_bytes 24 (reserved_24 record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 2 (second_reserved_2 record) ++
      encode_bytes 10 (buy_pan record) ++
      encode_bytes 10 (sell_pan record) ++
      encode_bytes 60 (reserved_60 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (token_no_value, bytes) =>
          match ContractDesc7.decode bytes with
          | None => None
          | Some (contract_desc_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (fill_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (fill_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (fill_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (mkt_type_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (buy_open_close_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (reserved_4_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (buy_broker_id_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (sell_broker_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (trader_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (requested_by_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (sell_open_close_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (buy_account_number_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (sell_account_number_value, bytes) =>
                                                                  match decode_bytes 24 bytes with
                                                                  | None => None
                                                                  | Some (reserved_24_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (reserved_2_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (second_reserved_2_value, bytes) =>
                                                                              match decode_bytes 10 bytes with
                                                                              | None => None
                                                                              | Some (buy_pan_value, bytes) =>
                                                                                  match decode_bytes 10 bytes with
                                                                                  | None => None
                                                                                  | Some (sell_pan_value, bytes) =>
                                                                                      match decode_bytes 60 bytes with
                                                                                      | None => None
                                                                                      | Some (reserved_60_value, bytes) =>
                                                                                          Some ({| token_no := token_no_value; contract_desc := contract_desc_value; fill_number := fill_number_value; fill_quantity := fill_quantity_value; fill_price := fill_price_value; mkt_type := mkt_type_value; buy_open_close := buy_open_close_value; reserved_4 := reserved_4_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value; sell_open_close := sell_open_close_value; buy_account_number := buy_account_number_value; sell_account_number := sell_account_number_value; reserved_24 := reserved_24_value; reserved_2 := reserved_2_value; second_reserved_2 := second_reserved_2_value; buy_pan := buy_pan_value; sell_pan := sell_pan_value; reserved_60 := reserved_60_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 194.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ContractDesc7.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite ContractDesc7.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ContractDesc7.eq_dec]. Defined.

  End TradeInquiryMessage.

  Module ContractDesc8.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc8.

  Module ContractDesc9.

    (** CONTRACT_DESC *)
    Record t := {
      instrument_name : list byte;
      symbol : list byte;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      ca_level : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_name record) = 6 /\
      Datatypes.length (symbol record) = 10 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 2 /\
      (ca_level record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (instrument_name record) ++
      encode_bytes 10 (symbol record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 2 (option_type record) ++
      encode_uint 2 (ca_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (instrument_name_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (expiry_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ca_level_value, bytes) =>
                              Some ({| instrument_name := instrument_name_value; symbol := symbol_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; ca_level := ca_level_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDesc9.

  Module SecureBoxRegistrationRequestInMessage.

    (** Registers the box with the allocated gateway server *)
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

  End SecureBoxRegistrationRequestInMessage.

  Module BoxSignOnRequestInMessage.

    (** Signs the box on to the allocated gateway server *)
    Record t := {
      box_id : N;
      broker_id : list byte;
      reserved_5 : N;
      session_key : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (box_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (broker_id record) = 5 /\
      (reserved_5 record < 256 ^ N.of_nat 5)%N /\
      Datatypes.length (session_key record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (box_id record) ++
      encode_bytes 5 (broker_id record) ++
      encode_uint 5 (reserved_5 record) ++
      encode_bytes 8 (session_key record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (box_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (broker_id_value, bytes) =>
              match decode_uint 5 bytes with
              | None => None
              | Some (reserved_5_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (session_key_value, bytes) =>
                      Some ({| box_id := box_id_value; broker_id := broker_id_value; reserved_5 := reserved_5_value; session_key := session_key_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BoxSignOnRequestInMessage.

  Module BoxSignOffMessage.

    (** Signs the box off the gateway server *)
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

  Module ResetUserPasswordMessage.

    (** Requests a reset of the user password *)
    Record t := {
      user_id : N;
      reserved_14 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_14 record) = 14.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 14 (reserved_14 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (reserved_14_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_14 := reserved_14_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End ResetUserPasswordMessage.

  Module CollateralUserStatusChangeRequestMessage.

    (** Changes the collateral status of a user *)
    Record t := {
      user_id : N;
      col_user_bit : list byte;
      reserved_7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (col_user_bit record) = 1 /\
      (reserved_7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (col_user_bit record) ++
      encode_uint 7 (reserved_7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (col_user_bit_value, bytes) =>
              match decode_uint 7 bytes with
              | None => None
              | Some (reserved_7_value, bytes) =>
                  Some ({| user_id := user_id_value; col_user_bit := col_user_bit_value; reserved_7 := reserved_7_value |}, bytes)
              end
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CollateralUserStatusChangeRequestMessage.

  Module UserTradeModifyCancelStatusChangeRequestMessage.

    (** Changes whether a user may modify or cancel trades *)
    Record t := {
      user_id : N;
      trd_mod_cxl_bit : list byte;
      reserved_7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trd_mod_cxl_bit record) = 1 /\
      (reserved_7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 1 (trd_mod_cxl_bit record) ++
      encode_uint 7 (reserved_7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trd_mod_cxl_bit_value, bytes) =>
              match decode_uint 7 bytes with
              | None => None
              | Some (reserved_7_value, bytes) =>
                  Some ({| user_id := user_id_value; trd_mod_cxl_bit := trd_mod_cxl_bit_value; reserved_7 := reserved_7_value |}, bytes)
              end
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UserTradeModifyCancelStatusChangeRequestMessage.

  Module UserAddressUnlockRequestMessage.

    (** Requests that a locked user address be unlocked *)
    Record t := {
      user_id : N;
      reserved_70 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_70 record) = 70.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 70 (reserved_70 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 70 bytes with
          | None => None
          | Some (reserved_70_value, bytes) =>
              Some ({| user_id := user_id_value; reserved_70 := reserved_70_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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

  End UserAddressUnlockRequestMessage.

End NseFoOrderEntryV950Client.
