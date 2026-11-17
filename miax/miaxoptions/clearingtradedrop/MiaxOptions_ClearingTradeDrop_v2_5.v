From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Clearing Trade Drop

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
      - a length prefix framing what follows

    License: MIT No Attribution
  *)

Module MiaxOptionsClearingTradeDropV25.

  Module SesmPacketHeader.

    (** SesM packet header *)
    Record t := {
      sesm_packet_length : N;
      sesm_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sesm_packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sesm_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (sesm_packet_length record) ++
      encode_bytes 1 (sesm_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (sesm_packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sesm_packet_type_value, bytes) =>
              Some ({| sesm_packet_length := sesm_packet_length_value; sesm_packet_type := sesm_packet_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SesmPacketHeader.

  Module SystemState.

    (** This message format is used to notify firms of the state changes of the system. Firms can use notifications as triggers in their system to ensure electronic synchronization of systems. *)
    Record t := {
      notification_time : N;
      ctd_version : list byte;
      trading_session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (notification_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ctd_version record) = 8 /\
      (trading_session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (notification_time record) ++
      encode_bytes 8 (ctd_version record) ++
      encode_uint_le 4 (trading_session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (notification_time_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (ctd_version_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (trading_session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| notification_time := notification_time_value; ctd_version := ctd_version_value; trading_session_id := trading_session_id_value; system_status := system_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemState.

  Module TradeMessage.

    (** This is the message format that will be used to disseminate all MIAX trade related content for entitled parties. MIAX sends trades, trade corrections and trade cancels using this message. This is a sequenced message. *)
    Record t := {
      processing_time : N;
      trade_time : N;
      trade_as_of_date : N;
      trade_action : list byte;
      trade_type : list byte;
      trade_id : N;
      execution_id : N;
      correction_number : N;
      transaction_id : N;
      reference_trade_time : N;
      reference_trade_id : N;
      reference_correction_number : N;
      correction_type : list byte;
      event_id : N;
      strategy_id : N;
      reserved_12 : list byte;
      product_id : N;
      underlying_symbol : list byte;
      underlying_type : list byte;
      security_symbol : list byte;
      expiration_date : N;
      strike_price : N;
      call_or_put : list byte;
      reserved_8 : list byte;
      side : list byte;
      price : N;
      size : N;
      trade_condition : list byte;
      second_reserved_8 : list byte;
      class_fee_type : list byte;
      miax_bbo_posting_increment_indicator : list byte;
      execution_exchange : list byte;
      routed_order_quantity : N;
      market_maker_role : list byte;
      traded_with_directed_mm : list byte;
      market_state : list byte;
      auction_type : list byte;
      directed_status : list byte;
      strategy_state : list byte;
      strategy_auction_type : list byte;
      stock_execution_destination : list byte;
      reserved_13 : list byte;
      executing_mpid : list byte;
      order_date : N;
      fix_order_id : list byte;
      client_message_id : N;
      bulk_quote_index : N;
      open_close_indicator : list byte;
      liquidity_type : list byte;
      mm_priority_indicator : list byte;
      liquidity_indicator : list byte;
      liquidity_timer_role : list byte;
      time_in_force : list byte;
      billing_mpid : list byte;
      leg_reference_id : list byte;
      strategy_timer_role : list byte;
      stock_short_sell_indicator : list byte;
      reserved_4 : list byte;
      clearing_mpid : list byte;
      member_type : list byte;
      origin : list byte;
      clearing_number : N;
      cmta : N;
      multi_account : list byte;
      account_id : list byte;
      supplementary_id : list byte;
      allocation_id : list byte;
      billing_clearing_number : N;
      order_capacity : list byte;
      reserved_7 : list byte;
      mpid : list byte;
      contra_member_type : list byte;
      contra_origin : list byte;
      contra_clearing_number : N;
      contra_cmta : N;
      contra_time_in_force : list byte;
      contra_liquidity_timer_role : list byte;
      contra_strategy_timer_role : list byte;
      contra_order_capacity : list byte;
      second_reserved_12 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (processing_time record < 256 ^ N.of_nat 8)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N /\
      (trade_as_of_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_action record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      (correction_number record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (reference_trade_time record < 256 ^ N.of_nat 8)%N /\
      (reference_trade_id record < 256 ^ N.of_nat 4)%N /\
      (reference_correction_number record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (correction_type record) = 1 /\
      (event_id record < 256 ^ N.of_nat 4)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_12 record) = 12 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (underlying_type record) = 1 /\
      Datatypes.length (security_symbol record) = 6 /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (call_or_put record) = 1 /\
      Datatypes.length (reserved_8 record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1 /\
      Datatypes.length (second_reserved_8 record) = 8 /\
      Datatypes.length (class_fee_type record) = 1 /\
      Datatypes.length (miax_bbo_posting_increment_indicator record) = 1 /\
      Datatypes.length (execution_exchange record) = 1 /\
      (routed_order_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_maker_role record) = 1 /\
      Datatypes.length (traded_with_directed_mm record) = 1 /\
      Datatypes.length (market_state record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (directed_status record) = 1 /\
      Datatypes.length (strategy_state record) = 1 /\
      Datatypes.length (strategy_auction_type record) = 1 /\
      Datatypes.length (stock_execution_destination record) = 1 /\
      Datatypes.length (reserved_13 record) = 13 /\
      Datatypes.length (executing_mpid record) = 4 /\
      (order_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (fix_order_id record) = 30 /\
      (client_message_id record < 256 ^ N.of_nat 4)%N /\
      (bulk_quote_index record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (open_close_indicator record) = 1 /\
      Datatypes.length (liquidity_type record) = 1 /\
      Datatypes.length (mm_priority_indicator record) = 1 /\
      Datatypes.length (liquidity_indicator record) = 1 /\
      Datatypes.length (liquidity_timer_role record) = 1 /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (billing_mpid record) = 4 /\
      Datatypes.length (leg_reference_id record) = 5 /\
      Datatypes.length (strategy_timer_role record) = 1 /\
      Datatypes.length (stock_short_sell_indicator record) = 1 /\
      Datatypes.length (reserved_4 record) = 4 /\
      Datatypes.length (clearing_mpid record) = 4 /\
      Datatypes.length (member_type record) = 1 /\
      Datatypes.length (origin record) = 1 /\
      (clearing_number record < 256 ^ N.of_nat 4)%N /\
      (cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (multi_account record) = 5 /\
      Datatypes.length (account_id record) = 10 /\
      Datatypes.length (supplementary_id record) = 13 /\
      Datatypes.length (allocation_id record) = 4 /\
      (billing_clearing_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_capacity record) = 1 /\
      Datatypes.length (reserved_7 record) = 7 /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (contra_member_type record) = 1 /\
      Datatypes.length (contra_origin record) = 1 /\
      (contra_clearing_number record < 256 ^ N.of_nat 4)%N /\
      (contra_cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (contra_time_in_force record) = 1 /\
      Datatypes.length (contra_liquidity_timer_role record) = 1 /\
      Datatypes.length (contra_strategy_timer_role record) = 1 /\
      Datatypes.length (contra_order_capacity record) = 1 /\
      Datatypes.length (second_reserved_12 record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (processing_time record) ++
      encode_uint_le 8 (trade_time record) ++
      encode_uint_le 4 (trade_as_of_date record) ++
      encode_bytes 1 (trade_action record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint_le 4 (trade_id record) ++
      encode_uint_le 8 (execution_id record) ++
      encode_uint 1 (correction_number record) ++
      encode_uint_le 4 (transaction_id record) ++
      encode_uint_le 8 (reference_trade_time record) ++
      encode_uint_le 4 (reference_trade_id record) ++
      encode_uint 1 (reference_correction_number record) ++
      encode_bytes 1 (correction_type record) ++
      encode_uint_le 4 (event_id record) ++
      encode_uint_le 4 (strategy_id record) ++
      encode_bytes 12 (reserved_12 record) ++
      encode_uint_le 4 (product_id record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (underlying_type record) ++
      encode_bytes 6 (security_symbol record) ++
      encode_uint_le 4 (expiration_date record) ++
      encode_uint_le 4 (strike_price record) ++
      encode_bytes 1 (call_or_put record) ++
      encode_bytes 8 (reserved_8 record) ++
      encode_bytes 1 (side record) ++
      encode_uint_le 4 (price record) ++
      encode_uint_le 4 (size record) ++
      encode_bytes 1 (trade_condition record) ++
      encode_bytes 8 (second_reserved_8 record) ++
      encode_bytes 1 (class_fee_type record) ++
      encode_bytes 1 (miax_bbo_posting_increment_indicator record) ++
      encode_bytes 1 (execution_exchange record) ++
      encode_uint_le 4 (routed_order_quantity record) ++
      encode_bytes 1 (market_maker_role record) ++
      encode_bytes 1 (traded_with_directed_mm record) ++
      encode_bytes 1 (market_state record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (directed_status record) ++
      encode_bytes 1 (strategy_state record) ++
      encode_bytes 1 (strategy_auction_type record) ++
      encode_bytes 1 (stock_execution_destination record) ++
      encode_bytes 13 (reserved_13 record) ++
      encode_bytes 4 (executing_mpid record) ++
      encode_uint_le 4 (order_date record) ++
      encode_bytes 30 (fix_order_id record) ++
      encode_uint_le 4 (client_message_id record) ++
      encode_uint 1 (bulk_quote_index record) ++
      encode_bytes 1 (open_close_indicator record) ++
      encode_bytes 1 (liquidity_type record) ++
      encode_bytes 1 (mm_priority_indicator record) ++
      encode_bytes 1 (liquidity_indicator record) ++
      encode_bytes 1 (liquidity_timer_role record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 4 (billing_mpid record) ++
      encode_bytes 5 (leg_reference_id record) ++
      encode_bytes 1 (strategy_timer_role record) ++
      encode_bytes 1 (stock_short_sell_indicator record) ++
      encode_bytes 4 (reserved_4 record) ++
      encode_bytes 4 (clearing_mpid record) ++
      encode_bytes 1 (member_type record) ++
      encode_bytes 1 (origin record) ++
      encode_uint_le 4 (clearing_number record) ++
      encode_uint_le 4 (cmta record) ++
      encode_bytes 5 (multi_account record) ++
      encode_bytes 10 (account_id record) ++
      encode_bytes 13 (supplementary_id record) ++
      encode_bytes 4 (allocation_id record) ++
      encode_uint_le 4 (billing_clearing_number record) ++
      encode_bytes 1 (order_capacity record) ++
      encode_bytes 7 (reserved_7 record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (contra_member_type record) ++
      encode_bytes 1 (contra_origin record) ++
      encode_uint_le 4 (contra_clearing_number record) ++
      encode_uint_le 4 (contra_cmta record) ++
      encode_bytes 1 (contra_time_in_force record) ++
      encode_bytes 1 (contra_liquidity_timer_role record) ++
      encode_bytes 1 (contra_strategy_timer_role record) ++
      encode_bytes 1 (contra_order_capacity record) ++
      encode_bytes 12 (second_reserved_12 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (processing_time_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (trade_time_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (trade_as_of_date_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trade_action_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (trade_type_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (trade_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (correction_number_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (transaction_id_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (reference_trade_time_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (reference_trade_id_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reference_correction_number_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (correction_type_value, bytes) =>
                                                          match decode_uint_le 4 bytes with
                                                          | None => None
                                                          | Some (event_id_value, bytes) =>
                                                              match decode_uint_le 4 bytes with
                                                              | None => None
                                                              | Some (strategy_id_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (reserved_12_value, bytes) =>
                                                                      match decode_uint_le 4 bytes with
                                                                      | None => None
                                                                      | Some (product_id_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (underlying_symbol_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (underlying_type_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (security_symbol_value, bytes) =>
                                                                                      match decode_uint_le 4 bytes with
                                                                                      | None => None
                                                                                      | Some (expiration_date_value, bytes) =>
                                                                                          match decode_uint_le 4 bytes with
                                                                                          | None => None
                                                                                          | Some (strike_price_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (call_or_put_value, bytes) =>
                                                                                                  match decode_bytes 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (reserved_8_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (side_value, bytes) =>
                                                                                                          match decode_uint_le 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (price_value, bytes) =>
                                                                                                              match decode_uint_le 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (size_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (trade_condition_value, bytes) =>
                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (second_reserved_8_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (class_fee_type_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (miax_bbo_posting_increment_indicator_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (execution_exchange_value, bytes) =>
                                                                                                                                      match decode_uint_le 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (routed_order_quantity_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (market_maker_role_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (traded_with_directed_mm_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (market_state_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (auction_type_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (directed_status_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (strategy_state_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (strategy_auction_type_value, bytes) =>
                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (stock_execution_destination_value, bytes) =>
                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (reserved_13_value, bytes) =>
                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (executing_mpid_value, bytes) =>
                                                                                                                                                                                  match decode_uint_le 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (order_date_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 30 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (fix_order_id_value, bytes) =>
                                                                                                                                                                                          match decode_uint_le 4 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (client_message_id_value, bytes) =>
                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bulk_quote_index_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (open_close_indicator_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (liquidity_type_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (mm_priority_indicator_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (liquidity_indicator_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (liquidity_timer_role_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (time_in_force_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (billing_mpid_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (leg_reference_id_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (strategy_timer_role_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (stock_short_sell_indicator_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (reserved_4_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (clearing_mpid_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (member_type_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (origin_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_uint_le 4 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (clearing_number_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint_le 4 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (cmta_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (multi_account_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 10 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (account_id_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (supplementary_id_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (allocation_id_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_uint_le 4 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (billing_clearing_number_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (order_capacity_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 7 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (reserved_7_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (mpid_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (contra_member_type_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (contra_origin_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint_le 4 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (contra_clearing_number_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_uint_le 4 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (contra_cmta_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (contra_time_in_force_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (contra_liquidity_timer_role_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (contra_strategy_timer_role_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (contra_order_capacity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (second_reserved_12_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      Some ({| processing_time := processing_time_value; trade_time := trade_time_value; trade_as_of_date := trade_as_of_date_value; trade_action := trade_action_value; trade_type := trade_type_value; trade_id := trade_id_value; execution_id := execution_id_value; correction_number := correction_number_value; transaction_id := transaction_id_value; reference_trade_time := reference_trade_time_value; reference_trade_id := reference_trade_id_value; reference_correction_number := reference_correction_number_value; correction_type := correction_type_value; event_id := event_id_value; strategy_id := strategy_id_value; reserved_12 := reserved_12_value; product_id := product_id_value; underlying_symbol := underlying_symbol_value; underlying_type := underlying_type_value; security_symbol := security_symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; call_or_put := call_or_put_value; reserved_8 := reserved_8_value; side := side_value; price := price_value; size := size_value; trade_condition := trade_condition_value; second_reserved_8 := second_reserved_8_value; class_fee_type := class_fee_type_value; miax_bbo_posting_increment_indicator := miax_bbo_posting_increment_indicator_value; execution_exchange := execution_exchange_value; routed_order_quantity := routed_order_quantity_value; market_maker_role := market_maker_role_value; traded_with_directed_mm := traded_with_directed_mm_value; market_state := market_state_value; auction_type := auction_type_value; directed_status := directed_status_value; strategy_state := strategy_state_value; strategy_auction_type := strategy_auction_type_value; stock_execution_destination := stock_execution_destination_value; reserved_13 := reserved_13_value; executing_mpid := executing_mpid_value; order_date := order_date_value; fix_order_id := fix_order_id_value; client_message_id := client_message_id_value; bulk_quote_index := bulk_quote_index_value; open_close_indicator := open_close_indicator_value; liquidity_type := liquidity_type_value; mm_priority_indicator := mm_priority_indicator_value; liquidity_indicator := liquidity_indicator_value; liquidity_timer_role := liquidity_timer_role_value; time_in_force := time_in_force_value; billing_mpid := billing_mpid_value; leg_reference_id := leg_reference_id_value; strategy_timer_role := strategy_timer_role_value; stock_short_sell_indicator := stock_short_sell_indicator_value; reserved_4 := reserved_4_value; clearing_mpid := clearing_mpid_value; member_type := member_type_value; origin := origin_value; clearing_number := clearing_number_value; cmta := cmta_value; multi_account := multi_account_value; account_id := account_id_value; supplementary_id := supplementary_id_value; allocation_id := allocation_id_value; billing_clearing_number := billing_clearing_number_value; order_capacity := order_capacity_value; reserved_7 := reserved_7_value; mpid := mpid_value; contra_member_type := contra_member_type_value; contra_origin := contra_origin_value; contra_clearing_number := contra_clearing_number_value; contra_cmta := contra_cmta_value; contra_time_in_force := contra_time_in_force_value; contra_liquidity_timer_role := contra_liquidity_timer_role_value; contra_strategy_timer_role := contra_strategy_timer_role_value; contra_order_capacity := contra_order_capacity_value; second_reserved_12 := second_reserved_12_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 310.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 bound_79]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint_le by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint_le by exact bound_20.
      rewrite decode_encode_uint_le by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint_le by exact bound_25.
      rewrite decode_encode_uint_le by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_uint_le by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_uint_le by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_uint_le by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_bytes by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_uint_le by exact bound_61.
      rewrite decode_encode_uint_le by exact bound_62.
      rewrite decode_encode_bytes by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_uint_le by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_bytes by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      rewrite decode_encode_bytes by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint_le by exact bound_73.
      rewrite decode_encode_uint_le by exact bound_74.
      rewrite decode_encode_bytes by exact bound_75.
      rewrite decode_encode_bytes by exact bound_76.
      rewrite decode_encode_bytes by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module RiskNotificationMessage.

    (** Firms configured to use Risk Protection Monitoring will receive User Notification communicating the status of Risk checks. Field Event Type is used to determine the reason for the notification. The following message will be used to disseminate all MIAX Risk Protection Monitor (RPM) related notifications. Sequenced and UnSequenced Pkt based on Event Type: solicited event types (T, R, W, D, A, P, U) are Sequenced messages at the SesM protocol level and recoverable; unsolicited (S) are Unsequenced and not recoverable. *)
    Record t := {
      processing_time : N;
      mpid_group_id : list byte;
      metric_id : list byte;
      route_id : list byte;
      metric_type : list byte;
      protection_type : list byte;
      event_type : list byte;
      event_id : N;
      configured_counting_time_period : N;
      configured_max_quantity : N;
      current_quantity : N;
      max_peak_quantity : N;
      percentage_level : N;
      reserved_32 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (processing_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid_group_id record) = 32 /\
      Datatypes.length (metric_id record) = 32 /\
      Datatypes.length (route_id record) = 32 /\
      Datatypes.length (metric_type record) = 1 /\
      Datatypes.length (protection_type record) = 1 /\
      Datatypes.length (event_type record) = 1 /\
      (event_id record < 256 ^ N.of_nat 4)%N /\
      (configured_counting_time_period record < 256 ^ N.of_nat 4)%N /\
      (configured_max_quantity record < 256 ^ N.of_nat 4)%N /\
      (current_quantity record < 256 ^ N.of_nat 4)%N /\
      (max_peak_quantity record < 256 ^ N.of_nat 4)%N /\
      (percentage_level record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_32 record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (processing_time record) ++
      encode_bytes 32 (mpid_group_id record) ++
      encode_bytes 32 (metric_id record) ++
      encode_bytes 32 (route_id record) ++
      encode_bytes 1 (metric_type record) ++
      encode_bytes 1 (protection_type record) ++
      encode_bytes 1 (event_type record) ++
      encode_uint_le 4 (event_id record) ++
      encode_uint_le 4 (configured_counting_time_period record) ++
      encode_uint_le 4 (configured_max_quantity record) ++
      encode_uint_le 4 (current_quantity record) ++
      encode_uint_le 4 (max_peak_quantity record) ++
      encode_uint 1 (percentage_level record) ++
      encode_bytes 32 (reserved_32 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (processing_time_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (mpid_group_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (metric_id_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (route_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (metric_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (protection_type_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (event_type_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (event_id_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (configured_counting_time_period_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (configured_max_quantity_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (current_quantity_value, bytes) =>
                                                  match decode_uint_le 4 bytes with
                                                  | None => None
                                                  | Some (max_peak_quantity_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (percentage_level_value, bytes) =>
                                                          match decode_bytes 32 bytes with
                                                          | None => None
                                                          | Some (reserved_32_value, bytes) =>
                                                              Some ({| processing_time := processing_time_value; mpid_group_id := mpid_group_id_value; metric_id := metric_id_value; route_id := route_id_value; metric_type := metric_type_value; protection_type := protection_type_value; event_type := event_type_value; event_id := event_id_value; configured_counting_time_period := configured_counting_time_period_value; configured_max_quantity := configured_max_quantity_value; current_quantity := current_quantity_value; max_peak_quantity := max_peak_quantity_value; percentage_level := percentage_level_value; reserved_32 := reserved_32_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RiskNotificationMessage.

  Module LoginRequest.

    (** The SesM client uses this packet to allow the server to authenticate the client and to convey to the server the last sequenced packet that the client received *)
    Record t := {
      sesm_version : list byte;
      username : list byte;
      computer_id : list byte;
      application_protocol : list byte;
      requested_session : N;
      requested_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sesm_version record) = 5 /\
      Datatypes.length (username record) = 5 /\
      Datatypes.length (computer_id record) = 8 /\
      Datatypes.length (application_protocol record) = 8 /\
      (requested_session record < 256 ^ N.of_nat 1)%N /\
      (requested_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (sesm_version record) ++
      encode_bytes 5 (username record) ++
      encode_bytes 8 (computer_id record) ++
      encode_bytes 8 (application_protocol record) ++
      encode_uint 1 (requested_session record) ++
      encode_uint_le 8 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (sesm_version_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (username_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (computer_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (application_protocol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (requested_session_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (requested_sequence_number_value, bytes) =>
                              Some ({| sesm_version := sesm_version_value; username := username_value; computer_id := computer_id_value; application_protocol := application_protocol_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !encode_uint_le_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequest.

  Module LoginResponse.

    (** The SesM server sends a Login response packet in response to a Login request packet from the client *)
    Record t := {
      login_status : list byte;
      session_id : N;
      highest_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_status record) = 1 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      (highest_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_status record) ++
      encode_uint 1 (session_id record) ++
      encode_uint_le 8 (highest_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_status_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (highest_sequence_number_value, bytes) =>
                  Some ({| login_status := login_status_value; session_id := session_id_value; highest_sequence_number := highest_sequence_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !encode_uint_le_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginResponse.

  Module RetransmissionRequest.

    (** The SesM client uses this packet to request the server to retransmit a range of packets *)
    Record t := {
      start_sequence_number : N;
      end_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (end_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (start_sequence_number record) ++
      encode_uint_le 8 (end_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (start_sequence_number_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (end_sequence_number_value, bytes) =>
              Some ({| start_sequence_number := start_sequence_number_value; end_sequence_number := end_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RetransmissionRequest.

End MiaxOptionsClearingTradeDropV25.
