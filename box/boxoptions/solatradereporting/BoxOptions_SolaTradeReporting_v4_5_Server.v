From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Box Options Market Sola Trade Reporting

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

Module BoxOptionsSolaTradeReportingV45Server.

  Module MessageHeader.

    (** Atr message header, twenty eight bytes opening every message either way *)
    Record t := {
      source : list byte;
      destination : list byte;
      message_type : list byte;
      message_flag : list byte;
      control_byte : list byte;
      sequence_number : list byte;
      acknowledgement_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (source record) = 4 /\
      Datatypes.length (destination record) = 4 /\
      Datatypes.length (message_type record) = 2 /\
      Datatypes.length (message_flag record) = 1 /\
      Datatypes.length (control_byte record) = 1 /\
      Datatypes.length (sequence_number record) = 8 /\
      Datatypes.length (acknowledgement_sequence_number record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (source record) ++
      encode_bytes 4 (destination record) ++
      encode_bytes 2 (message_type record) ++
      encode_bytes 1 (message_flag record) ++
      encode_bytes 1 (control_byte record) ++
      encode_bytes 8 (sequence_number record) ++
      encode_bytes 8 (acknowledgement_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (source_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (destination_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (message_flag_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (control_byte_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (sequence_number_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (acknowledgement_sequence_number_value, bytes) =>
                                  Some ({| source := source_value; destination := destination_value; message_type := message_type_value; message_flag := message_flag_value; control_byte := control_byte_value; sequence_number := sequence_number_value; acknowledgement_sequence_number := acknowledgement_sequence_number_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module ClientSignonAcknowledgment.

    Record t := {
      last_user_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (last_user_sequence_number record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (last_user_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (last_user_sequence_number_value, bytes) =>
          Some ({| last_user_sequence_number := last_user_sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End ClientSignonAcknowledgment.

  Module Trade.

    (** The guide heads this message 212 bytes, while the fields it states measure 228 including the 28 byte header. *)
    Record t := {
      trade_number : list byte;
      transaction_type : list byte;
      timestamp : list byte;
      symbol : list byte;
      expiration_date : list byte;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      option_type : list byte;
      volume : list byte;
      price : list byte;
      cmta_broker : list byte;
      account_type : list byte;
      sub_trader_id : list byte;
      open_close : list byte;
      executing_broker : list byte;
      client_account_number : list byte;
      client_order_id : list byte;
      client_memo : list byte;
      liquidity_status : list byte;
      trade_type : list byte;
      opposite_account_type : list byte;
      participant_session_name : list byte;
      unique_transaction_id : list byte;
      parent_transaction_id : list byte;
      opposite_executing_broker : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_number record) = 15 /\
      Datatypes.length (transaction_type record) = 1 /\
      Datatypes.length (timestamp record) = 6 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (expiration_date record) = 6 /\
      Datatypes.length (strike_price record) = 8 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (price record) = 8 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (executing_broker record) = 4 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (opposite_account_type record) = 1 /\
      Datatypes.length (participant_session_name record) = 12 /\
      Datatypes.length (unique_transaction_id record) = 10 /\
      Datatypes.length (parent_transaction_id record) = 10 /\
      Datatypes.length (opposite_executing_broker record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (trade_number record) ++
      encode_bytes 1 (transaction_type record) ++
      encode_bytes 6 (timestamp record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 6 (expiration_date record) ++
      encode_bytes 8 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 8 (price record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 4 (executing_broker record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 1 (opposite_account_type record) ++
      encode_bytes 12 (participant_session_name record) ++
      encode_bytes 10 (unique_transaction_id record) ++
      encode_bytes 10 (parent_transaction_id record) ++
      encode_bytes 4 (opposite_executing_broker record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (trade_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (transaction_type_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (strike_price_fraction_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (cmta_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (account_type_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (sub_trader_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (open_close_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (executing_broker_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (client_account_number_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (client_order_id_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (client_memo_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_type_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (opposite_account_type_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (participant_session_name_value, bytes) =>
                                                                                              match decode_bytes 10 bytes with
                                                                                              | None => None
                                                                                              | Some (unique_transaction_id_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (parent_transaction_id_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (opposite_executing_broker_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (additional_client_memo_value, bytes) =>
                                                                                                              Some ({| trade_number := trade_number_value; transaction_type := transaction_type_value; timestamp := timestamp_value; symbol := symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value; option_type := option_type_value; volume := volume_value; price := price_value; cmta_broker := cmta_broker_value; account_type := account_type_value; sub_trader_id := sub_trader_id_value; open_close := open_close_value; executing_broker := executing_broker_value; client_account_number := client_account_number_value; client_order_id := client_order_id_value; client_memo := client_memo_value; liquidity_status := liquidity_status_value; trade_type := trade_type_value; opposite_account_type := opposite_account_type_value; participant_session_name := participant_session_name_value; unique_transaction_id := unique_transaction_id_value; parent_transaction_id := parent_transaction_id_value; opposite_executing_broker := opposite_executing_broker_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 200.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Trade.

  Module TradeCancel.

    (** The guide states this message as having the same structure as message type 30, whose fields are written out here. The guide heads this message 212 bytes, while the fields it states measure 228 including the 28 byte header. *)
    Record t := {
      trade_number : list byte;
      transaction_type : list byte;
      timestamp : list byte;
      symbol : list byte;
      expiration_date : list byte;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      option_type : list byte;
      volume : list byte;
      price : list byte;
      cmta_broker : list byte;
      account_type : list byte;
      sub_trader_id : list byte;
      open_close : list byte;
      executing_broker : list byte;
      client_account_number : list byte;
      client_order_id : list byte;
      client_memo : list byte;
      liquidity_status : list byte;
      trade_type : list byte;
      opposite_account_type : list byte;
      participant_session_name : list byte;
      unique_transaction_id : list byte;
      parent_transaction_id : list byte;
      opposite_executing_broker : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_number record) = 15 /\
      Datatypes.length (transaction_type record) = 1 /\
      Datatypes.length (timestamp record) = 6 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (expiration_date record) = 6 /\
      Datatypes.length (strike_price record) = 8 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (price record) = 8 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (executing_broker record) = 4 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (opposite_account_type record) = 1 /\
      Datatypes.length (participant_session_name record) = 12 /\
      Datatypes.length (unique_transaction_id record) = 10 /\
      Datatypes.length (parent_transaction_id record) = 10 /\
      Datatypes.length (opposite_executing_broker record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (trade_number record) ++
      encode_bytes 1 (transaction_type record) ++
      encode_bytes 6 (timestamp record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 6 (expiration_date record) ++
      encode_bytes 8 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 8 (price record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 4 (executing_broker record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 1 (opposite_account_type record) ++
      encode_bytes 12 (participant_session_name record) ++
      encode_bytes 10 (unique_transaction_id record) ++
      encode_bytes 10 (parent_transaction_id record) ++
      encode_bytes 4 (opposite_executing_broker record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (trade_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (transaction_type_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (strike_price_fraction_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (cmta_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (account_type_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (sub_trader_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (open_close_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (executing_broker_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (client_account_number_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (client_order_id_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (client_memo_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_type_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (opposite_account_type_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (participant_session_name_value, bytes) =>
                                                                                              match decode_bytes 10 bytes with
                                                                                              | None => None
                                                                                              | Some (unique_transaction_id_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (parent_transaction_id_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (opposite_executing_broker_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (additional_client_memo_value, bytes) =>
                                                                                                              Some ({| trade_number := trade_number_value; transaction_type := transaction_type_value; timestamp := timestamp_value; symbol := symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value; option_type := option_type_value; volume := volume_value; price := price_value; cmta_broker := cmta_broker_value; account_type := account_type_value; sub_trader_id := sub_trader_id_value; open_close := open_close_value; executing_broker := executing_broker_value; client_account_number := client_account_number_value; client_order_id := client_order_id_value; client_memo := client_memo_value; liquidity_status := liquidity_status_value; trade_type := trade_type_value; opposite_account_type := opposite_account_type_value; participant_session_name := participant_session_name_value; unique_transaction_id := unique_transaction_id_value; parent_transaction_id := parent_transaction_id_value; opposite_executing_broker := opposite_executing_broker_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 200.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancel.

  Module Allocation.

    (** The guide states this message as having the same structure as message type 30, whose fields are written out here. The guide heads this message 212 bytes, while the fields it states measure 228 including the 28 byte header. *)
    Record t := {
      trade_number : list byte;
      transaction_type : list byte;
      timestamp : list byte;
      symbol : list byte;
      expiration_date : list byte;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      option_type : list byte;
      volume : list byte;
      price : list byte;
      cmta_broker : list byte;
      account_type : list byte;
      sub_trader_id : list byte;
      open_close : list byte;
      executing_broker : list byte;
      client_account_number : list byte;
      client_order_id : list byte;
      client_memo : list byte;
      liquidity_status : list byte;
      trade_type : list byte;
      opposite_account_type : list byte;
      participant_session_name : list byte;
      unique_transaction_id : list byte;
      parent_transaction_id : list byte;
      opposite_executing_broker : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_number record) = 15 /\
      Datatypes.length (transaction_type record) = 1 /\
      Datatypes.length (timestamp record) = 6 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (expiration_date record) = 6 /\
      Datatypes.length (strike_price record) = 8 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (price record) = 8 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (executing_broker record) = 4 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (opposite_account_type record) = 1 /\
      Datatypes.length (participant_session_name record) = 12 /\
      Datatypes.length (unique_transaction_id record) = 10 /\
      Datatypes.length (parent_transaction_id record) = 10 /\
      Datatypes.length (opposite_executing_broker record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (trade_number record) ++
      encode_bytes 1 (transaction_type record) ++
      encode_bytes 6 (timestamp record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 6 (expiration_date record) ++
      encode_bytes 8 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 8 (price record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 4 (executing_broker record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 1 (opposite_account_type record) ++
      encode_bytes 12 (participant_session_name record) ++
      encode_bytes 10 (unique_transaction_id record) ++
      encode_bytes 10 (parent_transaction_id record) ++
      encode_bytes 4 (opposite_executing_broker record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (trade_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (transaction_type_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (strike_price_fraction_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (cmta_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (account_type_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (sub_trader_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (open_close_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (executing_broker_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (client_account_number_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (client_order_id_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (client_memo_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_type_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (opposite_account_type_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (participant_session_name_value, bytes) =>
                                                                                              match decode_bytes 10 bytes with
                                                                                              | None => None
                                                                                              | Some (unique_transaction_id_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (parent_transaction_id_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (opposite_executing_broker_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (additional_client_memo_value, bytes) =>
                                                                                                              Some ({| trade_number := trade_number_value; transaction_type := transaction_type_value; timestamp := timestamp_value; symbol := symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value; option_type := option_type_value; volume := volume_value; price := price_value; cmta_broker := cmta_broker_value; account_type := account_type_value; sub_trader_id := sub_trader_id_value; open_close := open_close_value; executing_broker := executing_broker_value; client_account_number := client_account_number_value; client_order_id := client_order_id_value; client_memo := client_memo_value; liquidity_status := liquidity_status_value; trade_type := trade_type_value; opposite_account_type := opposite_account_type_value; participant_session_name := participant_session_name_value; unique_transaction_id := unique_transaction_id_value; parent_transaction_id := parent_transaction_id_value; opposite_executing_broker := opposite_executing_broker_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 200.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Allocation.

  Module AllocationCancel.

    (** The guide states this message as having the same structure as message type 30, whose fields are written out here. The guide heads this message 212 bytes, while the fields it states measure 228 including the 28 byte header. *)
    Record t := {
      trade_number : list byte;
      transaction_type : list byte;
      timestamp : list byte;
      symbol : list byte;
      expiration_date : list byte;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      option_type : list byte;
      volume : list byte;
      price : list byte;
      cmta_broker : list byte;
      account_type : list byte;
      sub_trader_id : list byte;
      open_close : list byte;
      executing_broker : list byte;
      client_account_number : list byte;
      client_order_id : list byte;
      client_memo : list byte;
      liquidity_status : list byte;
      trade_type : list byte;
      opposite_account_type : list byte;
      participant_session_name : list byte;
      unique_transaction_id : list byte;
      parent_transaction_id : list byte;
      opposite_executing_broker : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_number record) = 15 /\
      Datatypes.length (transaction_type record) = 1 /\
      Datatypes.length (timestamp record) = 6 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (expiration_date record) = 6 /\
      Datatypes.length (strike_price record) = 8 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (price record) = 8 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (executing_broker record) = 4 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (opposite_account_type record) = 1 /\
      Datatypes.length (participant_session_name record) = 12 /\
      Datatypes.length (unique_transaction_id record) = 10 /\
      Datatypes.length (parent_transaction_id record) = 10 /\
      Datatypes.length (opposite_executing_broker record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (trade_number record) ++
      encode_bytes 1 (transaction_type record) ++
      encode_bytes 6 (timestamp record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 6 (expiration_date record) ++
      encode_bytes 8 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 8 (price record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 4 (executing_broker record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 1 (opposite_account_type record) ++
      encode_bytes 12 (participant_session_name record) ++
      encode_bytes 10 (unique_transaction_id record) ++
      encode_bytes 10 (parent_transaction_id record) ++
      encode_bytes 4 (opposite_executing_broker record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (trade_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (transaction_type_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (strike_price_fraction_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (cmta_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (account_type_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (sub_trader_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (open_close_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (executing_broker_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (client_account_number_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (client_order_id_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (client_memo_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_type_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (opposite_account_type_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (participant_session_name_value, bytes) =>
                                                                                              match decode_bytes 10 bytes with
                                                                                              | None => None
                                                                                              | Some (unique_transaction_id_value, bytes) =>
                                                                                                  match decode_bytes 10 bytes with
                                                                                                  | None => None
                                                                                                  | Some (parent_transaction_id_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (opposite_executing_broker_value, bytes) =>
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (additional_client_memo_value, bytes) =>
                                                                                                              Some ({| trade_number := trade_number_value; transaction_type := transaction_type_value; timestamp := timestamp_value; symbol := symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value; option_type := option_type_value; volume := volume_value; price := price_value; cmta_broker := cmta_broker_value; account_type := account_type_value; sub_trader_id := sub_trader_id_value; open_close := open_close_value; executing_broker := executing_broker_value; client_account_number := client_account_number_value; client_order_id := client_order_id_value; client_memo := client_memo_value; liquidity_status := liquidity_status_value; trade_type := trade_type_value; opposite_account_type := opposite_account_type_value; participant_session_name := participant_session_name_value; unique_transaction_id := unique_transaction_id_value; parent_transaction_id := parent_transaction_id_value; opposite_executing_broker := opposite_executing_broker_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 200.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AllocationCancel.

  Module GiveUp.

    (** The guide heads this message 220 bytes, while the fields it states measure 236 including the 28 byte header. *)
    Record t := {
      trade_number : list byte;
      transaction_type : list byte;
      timestamp : list byte;
      symbol : list byte;
      expiration_date : list byte;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      option_type : list byte;
      volume : list byte;
      price : list byte;
      cmta_broker : list byte;
      account_type : list byte;
      sub_trader_id : list byte;
      open_close : list byte;
      executing_broker : list byte;
      client_account_number : list byte;
      client_order_id : list byte;
      client_memo : list byte;
      liquidity_status : list byte;
      trade_type : list byte;
      opposite_account_type : list byte;
      give_up_source : list byte;
      give_up_destination : list byte;
      participant_session_name : list byte;
      unique_transaction_id : list byte;
      parent_transaction_id : list byte;
      opposite_executing_broker : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_number record) = 15 /\
      Datatypes.length (transaction_type record) = 1 /\
      Datatypes.length (timestamp record) = 6 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (expiration_date record) = 6 /\
      Datatypes.length (strike_price record) = 8 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (price record) = 8 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (executing_broker record) = 4 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (opposite_account_type record) = 1 /\
      Datatypes.length (give_up_source record) = 4 /\
      Datatypes.length (give_up_destination record) = 4 /\
      Datatypes.length (participant_session_name record) = 12 /\
      Datatypes.length (unique_transaction_id record) = 10 /\
      Datatypes.length (parent_transaction_id record) = 10 /\
      Datatypes.length (opposite_executing_broker record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (trade_number record) ++
      encode_bytes 1 (transaction_type record) ++
      encode_bytes 6 (timestamp record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 6 (expiration_date record) ++
      encode_bytes 8 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 8 (price record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 4 (executing_broker record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 1 (opposite_account_type record) ++
      encode_bytes 4 (give_up_source record) ++
      encode_bytes 4 (give_up_destination record) ++
      encode_bytes 12 (participant_session_name record) ++
      encode_bytes 10 (unique_transaction_id record) ++
      encode_bytes 10 (parent_transaction_id record) ++
      encode_bytes 4 (opposite_executing_broker record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (trade_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (transaction_type_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (strike_price_fraction_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (cmta_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (account_type_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (sub_trader_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (open_close_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (executing_broker_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (client_account_number_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (client_order_id_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (client_memo_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_type_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (opposite_account_type_value, bytes) =>
                                                                                          match decode_bytes 4 bytes with
                                                                                          | None => None
                                                                                          | Some (give_up_source_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (give_up_destination_value, bytes) =>
                                                                                                  match decode_bytes 12 bytes with
                                                                                                  | None => None
                                                                                                  | Some (participant_session_name_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (unique_transaction_id_value, bytes) =>
                                                                                                          match decode_bytes 10 bytes with
                                                                                                          | None => None
                                                                                                          | Some (parent_transaction_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (opposite_executing_broker_value, bytes) =>
                                                                                                                  match decode_bytes 16 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (additional_client_memo_value, bytes) =>
                                                                                                                      Some ({| trade_number := trade_number_value; transaction_type := transaction_type_value; timestamp := timestamp_value; symbol := symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value; option_type := option_type_value; volume := volume_value; price := price_value; cmta_broker := cmta_broker_value; account_type := account_type_value; sub_trader_id := sub_trader_id_value; open_close := open_close_value; executing_broker := executing_broker_value; client_account_number := client_account_number_value; client_order_id := client_order_id_value; client_memo := client_memo_value; liquidity_status := liquidity_status_value; trade_type := trade_type_value; opposite_account_type := opposite_account_type_value; give_up_source := give_up_source_value; give_up_destination := give_up_destination_value; participant_session_name := participant_session_name_value; unique_transaction_id := unique_transaction_id_value; parent_transaction_id := parent_transaction_id_value; opposite_executing_broker := opposite_executing_broker_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 208.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GiveUp.

  Module GiveUpCancel.

    (** The guide states this message as having the same structure as message type 50, whose fields are written out here. The guide heads this message 216 bytes, while the fields it states measure 236 including the 28 byte header. *)
    Record t := {
      trade_number : list byte;
      transaction_type : list byte;
      timestamp : list byte;
      symbol : list byte;
      expiration_date : list byte;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      option_type : list byte;
      volume : list byte;
      price : list byte;
      cmta_broker : list byte;
      account_type : list byte;
      sub_trader_id : list byte;
      open_close : list byte;
      executing_broker : list byte;
      client_account_number : list byte;
      client_order_id : list byte;
      client_memo : list byte;
      liquidity_status : list byte;
      trade_type : list byte;
      opposite_account_type : list byte;
      give_up_source : list byte;
      give_up_destination : list byte;
      participant_session_name : list byte;
      unique_transaction_id : list byte;
      parent_transaction_id : list byte;
      opposite_executing_broker : list byte;
      additional_client_memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_number record) = 15 /\
      Datatypes.length (transaction_type record) = 1 /\
      Datatypes.length (timestamp record) = 6 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (expiration_date record) = 6 /\
      Datatypes.length (strike_price record) = 8 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (volume record) = 8 /\
      Datatypes.length (price record) = 8 /\
      Datatypes.length (cmta_broker record) = 4 /\
      Datatypes.length (account_type record) = 1 /\
      Datatypes.length (sub_trader_id record) = 3 /\
      Datatypes.length (open_close record) = 1 /\
      Datatypes.length (executing_broker record) = 4 /\
      Datatypes.length (client_account_number record) = 12 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (client_memo record) = 16 /\
      Datatypes.length (liquidity_status record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (opposite_account_type record) = 1 /\
      Datatypes.length (give_up_source record) = 4 /\
      Datatypes.length (give_up_destination record) = 4 /\
      Datatypes.length (participant_session_name record) = 12 /\
      Datatypes.length (unique_transaction_id record) = 10 /\
      Datatypes.length (parent_transaction_id record) = 10 /\
      Datatypes.length (opposite_executing_broker record) = 4 /\
      Datatypes.length (additional_client_memo record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (trade_number record) ++
      encode_bytes 1 (transaction_type record) ++
      encode_bytes 6 (timestamp record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 6 (expiration_date record) ++
      encode_bytes 8 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 8 (volume record) ++
      encode_bytes 8 (price record) ++
      encode_bytes 4 (cmta_broker record) ++
      encode_bytes 1 (account_type record) ++
      encode_bytes 3 (sub_trader_id record) ++
      encode_bytes 1 (open_close record) ++
      encode_bytes 4 (executing_broker record) ++
      encode_bytes 12 (client_account_number record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 16 (client_memo record) ++
      encode_bytes 1 (liquidity_status record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 1 (opposite_account_type record) ++
      encode_bytes 4 (give_up_source record) ++
      encode_bytes 4 (give_up_destination record) ++
      encode_bytes 12 (participant_session_name record) ++
      encode_bytes 10 (unique_transaction_id record) ++
      encode_bytes 10 (parent_transaction_id record) ++
      encode_bytes 4 (opposite_executing_broker record) ++
      encode_bytes 16 (additional_client_memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (trade_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (transaction_type_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (strike_price_fraction_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (cmta_broker_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (account_type_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (sub_trader_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (open_close_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (executing_broker_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (client_account_number_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (client_order_id_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (client_memo_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (liquidity_status_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_type_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (opposite_account_type_value, bytes) =>
                                                                                          match decode_bytes 4 bytes with
                                                                                          | None => None
                                                                                          | Some (give_up_source_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (give_up_destination_value, bytes) =>
                                                                                                  match decode_bytes 12 bytes with
                                                                                                  | None => None
                                                                                                  | Some (participant_session_name_value, bytes) =>
                                                                                                      match decode_bytes 10 bytes with
                                                                                                      | None => None
                                                                                                      | Some (unique_transaction_id_value, bytes) =>
                                                                                                          match decode_bytes 10 bytes with
                                                                                                          | None => None
                                                                                                          | Some (parent_transaction_id_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (opposite_executing_broker_value, bytes) =>
                                                                                                                  match decode_bytes 16 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (additional_client_memo_value, bytes) =>
                                                                                                                      Some ({| trade_number := trade_number_value; transaction_type := transaction_type_value; timestamp := timestamp_value; symbol := symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value; option_type := option_type_value; volume := volume_value; price := price_value; cmta_broker := cmta_broker_value; account_type := account_type_value; sub_trader_id := sub_trader_id_value; open_close := open_close_value; executing_broker := executing_broker_value; client_account_number := client_account_number_value; client_order_id := client_order_id_value; client_memo := client_memo_value; liquidity_status := liquidity_status_value; trade_type := trade_type_value; opposite_account_type := opposite_account_type_value; give_up_source := give_up_source_value; give_up_destination := give_up_destination_value; participant_session_name := participant_session_name_value; unique_transaction_id := unique_transaction_id_value; parent_transaction_id := parent_transaction_id_value; opposite_executing_broker := opposite_executing_broker_value; additional_client_memo := additional_client_memo_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 208.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GiveUpCancel.

  Module ErrorMessage.

    (** The guide heads this message up to 112 bytes, while the fields it states measure 114 including the 28 byte header. *)
    Record t := {
      reference_message_type : list byte;
      error_code : list byte;
      error_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_message_type record) = 2 /\
      Datatypes.length (error_code record) = 4 /\
      Datatypes.length (error_text record) = 80.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reference_message_type record) ++
      encode_bytes 4 (error_code record) ++
      encode_bytes 80 (error_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reference_message_type_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (error_code_value, bytes) =>
              match decode_bytes 80 bytes with
              | None => None
              | Some (error_text_value, bytes) =>
                  Some ({| reference_message_type := reference_message_type_value; error_code := error_code_value; error_text := error_text_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ErrorMessage.

End BoxOptionsSolaTradeReportingV45Server.
