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

    License: MIT No Attribution
  *)

Module NseComOrderEntryV35Client.

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

    (** 1600 MS_SYSTEM_INFO_REQ 44 I, carried in the MS_SYSTEM_INFO_REQ structure *)
    Record t := {
      last_update_portfolio_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_portfolio_time record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_update_portfolio_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_update_portfolio_time_value, bytes) =>
          Some ({| last_update_portfolio_time := last_update_portfolio_time_value |}, bytes)
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

  Module TradeCancelInMessage.

    (** 5440 MS_TRADE_INQ_DATA 234 I, carried in the MS_TRADE_INQ_DATA structure *)
    Record t := {
      token_no : N;
      contract_desc : ContractDesc.t;
      fill_number : N;
      fill_quantity : N;
      fill_price : N;
      mkt_type : list byte;
      buy_open_close : list byte;
      new_volume : N;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : list byte;
      sell_open_close : list byte;
      buy_account_number : list byte;
      sell_account_number : list byte;
      buy_participant : list byte;
      sell_participant : list byte;
      reserved_2 : N;
      buy_giveup_flag : list byte;
      sell_giveup_flag : list byte;
      buy_pan : list byte;
      sell_pan : list byte;
      reserved_60 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (token_no record < 256 ^ N.of_nat 4)%N /\
      ContractDesc.bounded (contract_desc record) /\
      (fill_number record < 256 ^ N.of_nat 4)%N /\
      (fill_quantity record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mkt_type record) = 1 /\
      Datatypes.length (buy_open_close record) = 1 /\
      (new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (requested_by record) = 1 /\
      Datatypes.length (sell_open_close record) = 1 /\
      Datatypes.length (buy_account_number record) = 10 /\
      Datatypes.length (sell_account_number record) = 10 /\
      Datatypes.length (buy_participant record) = 12 /\
      Datatypes.length (sell_participant record) = 12 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (buy_giveup_flag record) = 1 /\
      Datatypes.length (sell_giveup_flag record) = 1 /\
      Datatypes.length (buy_pan record) = 10 /\
      Datatypes.length (sell_pan record) = 10 /\
      Datatypes.length (reserved_60 record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (token_no record) ++
      ContractDesc.encode (contract_desc record) ++
      encode_uint 4 (fill_number record) ++
      encode_uint 4 (fill_quantity record) ++
      encode_uint 4 (fill_price record) ++
      encode_bytes 1 (mkt_type record) ++
      encode_bytes 1 (buy_open_close record) ++
      encode_uint 4 (new_volume record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_bytes 1 (requested_by record) ++
      encode_bytes 1 (sell_open_close record) ++
      encode_bytes 10 (buy_account_number record) ++
      encode_bytes 10 (sell_account_number record) ++
      encode_bytes 12 (buy_participant record) ++
      encode_bytes 12 (sell_participant record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_bytes 1 (buy_giveup_flag record) ++
      encode_bytes 1 (sell_giveup_flag record) ++
      encode_bytes 10 (buy_pan record) ++
      encode_bytes 10 (sell_pan record) ++
      encode_bytes 60 (reserved_60 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (token_no_value, bytes) =>
          match ContractDesc.decode bytes with
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
                                  | Some (new_volume_value, bytes) =>
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
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (buy_participant_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (sell_participant_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (reserved_2_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (buy_giveup_flag_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (sell_giveup_flag_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (buy_pan_value, bytes) =>
                                                                                          match decode_bytes 10 bytes with
                                                                                          | None => None
                                                                                          | Some (sell_pan_value, bytes) =>
                                                                                              match decode_bytes 60 bytes with
                                                                                              | None => None
                                                                                              | Some (reserved_60_value, bytes) =>
                                                                                                  Some ({| token_no := token_no_value; contract_desc := contract_desc_value; fill_number := fill_number_value; fill_quantity := fill_quantity_value; fill_price := fill_price_value; mkt_type := mkt_type_value; buy_open_close := buy_open_close_value; new_volume := new_volume_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value; sell_open_close := sell_open_close_value; buy_account_number := buy_account_number_value; sell_account_number := sell_account_number_value; buy_participant := buy_participant_value; sell_participant := sell_participant_value; reserved_2 := reserved_2_value; buy_giveup_flag := buy_giveup_flag_value; sell_giveup_flag := sell_giveup_flag_value; buy_pan := buy_pan_value; sell_pan := sell_pan_value; reserved_60 := reserved_60_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 194.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ContractDesc.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite ContractDesc.decode_encode by exact bound_1.
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
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ContractDesc.eq_dec]. Defined.

  End TradeCancelInMessage.

  Module TradeModInMessage.

    (** 5445 MS_TRADE_INQ_DATA 234 I, carried in the MS_TRADE_INQ_DATA structure *)
    Record t := {
      token_no : N;
      contract_desc : ContractDesc.t;
      fill_number : N;
      fill_quantity : N;
      fill_price : N;
      mkt_type : list byte;
      buy_open_close : list byte;
      new_volume : N;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
      trader_id : N;
      requested_by : list byte;
      sell_open_close : list byte;
      buy_account_number : list byte;
      sell_account_number : list byte;
      buy_participant : list byte;
      sell_participant : list byte;
      reserved_2 : N;
      buy_giveup_flag : list byte;
      sell_giveup_flag : list byte;
      buy_pan : list byte;
      sell_pan : list byte;
      reserved_60 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (token_no record < 256 ^ N.of_nat 4)%N /\
      ContractDesc.bounded (contract_desc record) /\
      (fill_number record < 256 ^ N.of_nat 4)%N /\
      (fill_quantity record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mkt_type record) = 1 /\
      Datatypes.length (buy_open_close record) = 1 /\
      (new_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_broker_id record) = 5 /\
      Datatypes.length (sell_broker_id record) = 5 /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (requested_by record) = 1 /\
      Datatypes.length (sell_open_close record) = 1 /\
      Datatypes.length (buy_account_number record) = 10 /\
      Datatypes.length (sell_account_number record) = 10 /\
      Datatypes.length (buy_participant record) = 12 /\
      Datatypes.length (sell_participant record) = 12 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (buy_giveup_flag record) = 1 /\
      Datatypes.length (sell_giveup_flag record) = 1 /\
      Datatypes.length (buy_pan record) = 10 /\
      Datatypes.length (sell_pan record) = 10 /\
      Datatypes.length (reserved_60 record) = 60.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (token_no record) ++
      ContractDesc.encode (contract_desc record) ++
      encode_uint 4 (fill_number record) ++
      encode_uint 4 (fill_quantity record) ++
      encode_uint 4 (fill_price record) ++
      encode_bytes 1 (mkt_type record) ++
      encode_bytes 1 (buy_open_close record) ++
      encode_uint 4 (new_volume record) ++
      encode_bytes 5 (buy_broker_id record) ++
      encode_bytes 5 (sell_broker_id record) ++
      encode_uint 4 (trader_id record) ++
      encode_bytes 1 (requested_by record) ++
      encode_bytes 1 (sell_open_close record) ++
      encode_bytes 10 (buy_account_number record) ++
      encode_bytes 10 (sell_account_number record) ++
      encode_bytes 12 (buy_participant record) ++
      encode_bytes 12 (sell_participant record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_bytes 1 (buy_giveup_flag record) ++
      encode_bytes 1 (sell_giveup_flag record) ++
      encode_bytes 10 (buy_pan record) ++
      encode_bytes 10 (sell_pan record) ++
      encode_bytes 60 (reserved_60 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (token_no_value, bytes) =>
          match ContractDesc.decode bytes with
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
                                  | Some (new_volume_value, bytes) =>
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
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (buy_participant_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (sell_participant_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (reserved_2_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (buy_giveup_flag_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (sell_giveup_flag_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (buy_pan_value, bytes) =>
                                                                                          match decode_bytes 10 bytes with
                                                                                          | None => None
                                                                                          | Some (sell_pan_value, bytes) =>
                                                                                              match decode_bytes 60 bytes with
                                                                                              | None => None
                                                                                              | Some (reserved_60_value, bytes) =>
                                                                                                  Some ({| token_no := token_no_value; contract_desc := contract_desc_value; fill_number := fill_number_value; fill_quantity := fill_quantity_value; fill_price := fill_price_value; mkt_type := mkt_type_value; buy_open_close := buy_open_close_value; new_volume := new_volume_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value; trader_id := trader_id_value; requested_by := requested_by_value; sell_open_close := sell_open_close_value; buy_account_number := buy_account_number_value; sell_account_number := sell_account_number_value; buy_participant := buy_participant_value; sell_participant := sell_participant_value; reserved_2 := reserved_2_value; buy_giveup_flag := buy_giveup_flag_value; sell_giveup_flag := sell_giveup_flag_value; buy_pan := buy_pan_value; sell_pan := sell_pan_value; reserved_60 := reserved_60_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 194.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ContractDesc.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite ContractDesc.decode_encode by exact bound_1.
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
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ContractDesc.eq_dec]. Defined.

  End TradeModInMessage.

  Module GrRequestMessage.

    (** 2400 MS_GR_REQUEST 48 I, carried in the MS_GR_REQUEST structure *)
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

  End GrRequestMessage.

  Module UserAddrUnlockInMessage.

    (** 5427 USER_ADDR_UNLOCK_REQ_F 114 I O, carried in the USER_ADDR_UNLOCK_REQ_FO structure *)
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

  End UserAddrUnlockInMessage.

  Module ResetUserPasswordInMessage.

    (** 5740 RESET_USER_PASSWORD_IN_ 58 I FO, carried in the RESET_USER_PASSWORD_IN_FO structure *)
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

  End ResetUserPasswordInMessage.

  Module ColUserStatusChangeInMessage.

    (** 5744 COL_USER_STATUS_CHANGE_ 52 I REQ, carried in the COL_USER_STATUS_CHANGE_REQ structure *)
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

  End ColUserStatusChangeInMessage.

  Module StMarketStatus.

    (** ST_MARKET_STATUS *)
    Record t := {
      normal : N;
      oddlot : N;
      spot : N;
      auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (normal record < 256 ^ N.of_nat 2)%N /\
      (oddlot record < 256 ^ N.of_nat 2)%N /\
      (spot record < 256 ^ N.of_nat 2)%N /\
      (auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (normal record) ++
      encode_uint 2 (oddlot record) ++
      encode_uint 2 (spot record) ++
      encode_uint 2 (auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (auction_value, bytes) =>
                      Some ({| normal := normal_value; oddlot := oddlot_value; spot := spot_value; auction := auction_value |}, bytes)
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
      normal : N;
      oddlot : N;
      spot : N;
      auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (normal record < 256 ^ N.of_nat 2)%N /\
      (oddlot record < 256 ^ N.of_nat 2)%N /\
      (spot record < 256 ^ N.of_nat 2)%N /\
      (auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (normal record) ++
      encode_uint 2 (oddlot record) ++
      encode_uint 2 (spot record) ++
      encode_uint 2 (auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (auction_value, bytes) =>
                      Some ({| normal := normal_value; oddlot := oddlot_value; spot := spot_value; auction := auction_value |}, bytes)
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
      normal : N;
      oddlot : N;
      spot : N;
      auction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (normal record < 256 ^ N.of_nat 2)%N /\
      (oddlot record < 256 ^ N.of_nat 2)%N /\
      (spot record < 256 ^ N.of_nat 2)%N /\
      (auction record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (normal record) ++
      encode_uint 2 (oddlot record) ++
      encode_uint 2 (spot record) ++
      encode_uint 2 (auction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (normal_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (oddlot_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (spot_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (auction_value, bytes) =>
                      Some ({| normal := normal_value; oddlot := oddlot_value; spot := spot_value; auction := auction_value |}, bytes)
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

  Module UpdateLocaldbInMessage.

    (** 7300 MS_UPDATE_LOCAL_DATABA 82 I SE, carried in the MS_UPDATE_LOCAL_DATABASE structure *)
    Record t := {
      last_update_security_time : N;
      last_update_participant_time : N;
      last_update_instrument_time : N;
      last_update_index_time : N;
      request_for_open_orders : list byte;
      c_filler : list byte;
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
      Datatypes.length (c_filler record) = 1 /\
      StMarketStatus.bounded (st_market_status record) /\
      StExMarketStatus.bounded (st_ex_market_status record) /\
      StPlMarketStatus.bounded (st_pl_market_status record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_update_security_time record) ++
      encode_uint 4 (last_update_participant_time record) ++
      encode_uint 4 (last_update_instrument_time record) ++
      encode_uint 4 (last_update_index_time record) ++
      encode_bytes 1 (request_for_open_orders record) ++
      encode_bytes 1 (c_filler record) ++
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
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (c_filler_value, bytes) =>
                              match StMarketStatus.decode bytes with
                              | None => None
                              | Some (st_market_status_value, bytes) =>
                                  match StExMarketStatus.decode bytes with
                                  | None => None
                                  | Some (st_ex_market_status_value, bytes) =>
                                      match StPlMarketStatus.decode bytes with
                                      | None => None
                                      | Some (st_pl_market_status_value, bytes) =>
                                          Some ({| last_update_security_time := last_update_security_time_value; last_update_participant_time := last_update_participant_time_value; last_update_instrument_time := last_update_instrument_time_value; last_update_index_time := last_update_index_time_value; request_for_open_orders := request_for_open_orders_value; c_filler := c_filler_value; st_market_status := st_market_status_value; st_ex_market_status := st_ex_market_status_value; st_pl_market_status := st_pl_market_status_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite StMarketStatus.decode_encode by exact bound_6.
      rewrite StExMarketStatus.decode_encode by exact bound_7.
      rewrite StPlMarketStatus.decode_encode by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply StMarketStatus.eq_dec | apply StExMarketStatus.eq_dec | apply StPlMarketStatus.eq_dec]. Defined.

  End UpdateLocaldbInMessage.

  Module BoxSignOnRequestInMessage.

    (** 23000 MS_BOX_SIGN_ON_REQUEST 60 I _IN Confidential Commodity Derivatives Trading System - Protocol for Non-Neat Front End, carried in the MS_BOX_SIGN_ON_REQUEST_IN structure *)
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

  Module SecureBoxRegistrationRequestInMessage.

    (** Secure Box Registration Request In, carried in the MS_SECURE_BOX_REGISTRATION_REQUEST_IN structure *)
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

End NseComOrderEntryV35Client.
