From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Databento Normalized

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
      - a Composite rule
  *)

Module DatabentoMarketDataNormalizedV1GatewayStream.

  Module RecordHeader.

    (** DBN common header of every record *)
    Record t := {
      record_length : N;
      rtype : N;
      publisher_id : N;
      instrument_id : N;
      ts_event : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (record_length record < 256 ^ N.of_nat 1)%N /\
      (rtype record < 256 ^ N.of_nat 1)%N /\
      (publisher_id record < 256 ^ N.of_nat 2)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (ts_event record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (record_length record) ++
      encode_uint 1 (rtype record) ++
      encode_uint 2 (publisher_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (ts_event record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (record_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (rtype_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (publisher_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (ts_event_value, bytes) =>
                          Some ({| record_length := record_length_value; rtype := rtype_value; publisher_id := publisher_id_value; instrument_id := instrument_id_value; ts_event := ts_event_value |}, bytes)
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

  End RecordHeader.

  Module BidAskPair.

    (** A level *)
    Record t := {
      bid_px : N;
      ask_px : N;
      bid_sz : N;
      ask_sz : N;
      bid_ct : N;
      ask_ct : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (bid_px record < 256 ^ N.of_nat 8)%N /\
      (ask_px record < 256 ^ N.of_nat 8)%N /\
      (bid_sz record < 256 ^ N.of_nat 4)%N /\
      (ask_sz record < 256 ^ N.of_nat 4)%N /\
      (bid_ct record < 256 ^ N.of_nat 4)%N /\
      (ask_ct record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (bid_px record) ++
      encode_uint 8 (ask_px record) ++
      encode_uint 4 (bid_sz record) ++
      encode_uint 4 (ask_sz record) ++
      encode_uint 4 (bid_ct record) ++
      encode_uint 4 (ask_ct record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (bid_px_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (ask_px_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_sz_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_sz_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_ct_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ask_ct_value, bytes) =>
                              Some ({| bid_px := bid_px_value; ask_px := ask_px_value; bid_sz := bid_sz_value; ask_sz := ask_sz_value; bid_ct := bid_ct_value; ask_ct := ask_ct_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BidAskPair.

  Module OhlcvMsg.

    (** Open, high, low, close, and volume; the record of the ohlcv schemas *)
    Record t := {
      open : N;
      high : N;
      low : N;
      close : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (open record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (close record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (open record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (close record) ++
      encode_uint 8 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (open_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (high_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (low_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (close_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          Some ({| open := open_value; high := high_value; low := low_value; close := close_value; volume := volume_value |}, bytes)
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

  End OhlcvMsg.

  Module StatusMsg.

    (** A trading status update message; the record of the status schema *)
    Record t := {
      ts_recv : N;
      status_action : N;
      status_reason : N;
      trading_event : N;
      is_trading : list byte;
      is_quoting : list byte;
      is_short_sell_restricted : list byte;
      reserved_7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ts_recv record < 256 ^ N.of_nat 8)%N /\
      (status_action record < 256 ^ N.of_nat 2)%N /\
      (status_reason record < 256 ^ N.of_nat 2)%N /\
      (trading_event record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (is_trading record) = 1 /\
      Datatypes.length (is_quoting record) = 1 /\
      Datatypes.length (is_short_sell_restricted record) = 1 /\
      (reserved_7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (ts_recv record) ++
      encode_uint 2 (status_action record) ++
      encode_uint 2 (status_reason record) ++
      encode_uint 2 (trading_event record) ++
      encode_bytes 1 (is_trading record) ++
      encode_bytes 1 (is_quoting record) ++
      encode_bytes 1 (is_short_sell_restricted record) ++
      encode_uint 7 (reserved_7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (ts_recv_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (status_action_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (status_reason_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (trading_event_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (is_trading_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (is_quoting_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (is_short_sell_restricted_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (reserved_7_value, bytes) =>
                                      Some ({| ts_recv := ts_recv_value; status_action := status_action_value; status_reason := status_reason_value; trading_event := trading_event_value; is_trading := is_trading_value; is_quoting := is_quoting_value; is_short_sell_restricted := is_short_sell_restricted_value; reserved_7 := reserved_7_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatusMsg.

  Module InstrumentDefMsg.

    (** A definition of an instrument; the record of the definition schema *)
    Record t := {
      ts_recv : N;
      min_price_increment : N;
      display_factor : N;
      expiration : N;
      activation : N;
      high_limit_price : N;
      low_limit_price : N;
      max_price_variation : N;
      trading_reference_price : N;
      unit_of_measure_qty : N;
      min_price_increment_amount : N;
      price_ratio : N;
      inst_attrib_value : N;
      underlying_id : N;
      raw_instrument_id : N;
      market_depth_implied : N;
      market_depth : N;
      market_segment_id : N;
      max_trade_vol : N;
      min_lot_size : N;
      min_lot_size_block : N;
      min_lot_size_round_lot : N;
      min_trade_vol : N;
      reserved_4 : N;
      contract_multiplier : N;
      decay_quantity : N;
      original_contract_size : N;
      second_reserved_4 : N;
      trading_reference_date : N;
      appl_id : N;
      maturity_year : N;
      decay_start_date : N;
      channel : N;
      currency : list byte;
      settl_currency : list byte;
      secsubtype : list byte;
      raw_symbol : list byte;
      group : list byte;
      exchange : list byte;
      asset : list byte;
      cfi : list byte;
      security_type : list byte;
      unit_of_measure : list byte;
      underlying : list byte;
      strike_price_currency : list byte;
      instrument_class : list byte;
      reserved_2 : N;
      strike_price : N;
      reserved_6 : N;
      match_algorithm : list byte;
      md_security_trading_status : N;
      main_fraction : N;
      price_display_format : N;
      settl_price_type : N;
      sub_fraction : N;
      underlying_product : N;
      security_update_action : list byte;
      maturity_month : N;
      maturity_day : N;
      maturity_week : N;
      user_defined_instrument : list byte;
      contract_multiplier_unit : N;
      flow_schedule_type : N;
      tick_rule : N;
      dummy_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ts_recv record < 256 ^ N.of_nat 8)%N /\
      (min_price_increment record < 256 ^ N.of_nat 8)%N /\
      (display_factor record < 256 ^ N.of_nat 8)%N /\
      (expiration record < 256 ^ N.of_nat 8)%N /\
      (activation record < 256 ^ N.of_nat 8)%N /\
      (high_limit_price record < 256 ^ N.of_nat 8)%N /\
      (low_limit_price record < 256 ^ N.of_nat 8)%N /\
      (max_price_variation record < 256 ^ N.of_nat 8)%N /\
      (trading_reference_price record < 256 ^ N.of_nat 8)%N /\
      (unit_of_measure_qty record < 256 ^ N.of_nat 8)%N /\
      (min_price_increment_amount record < 256 ^ N.of_nat 8)%N /\
      (price_ratio record < 256 ^ N.of_nat 8)%N /\
      (inst_attrib_value record < 256 ^ N.of_nat 4)%N /\
      (underlying_id record < 256 ^ N.of_nat 4)%N /\
      (raw_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (market_depth_implied record < 256 ^ N.of_nat 4)%N /\
      (market_depth record < 256 ^ N.of_nat 4)%N /\
      (market_segment_id record < 256 ^ N.of_nat 4)%N /\
      (max_trade_vol record < 256 ^ N.of_nat 4)%N /\
      (min_lot_size record < 256 ^ N.of_nat 4)%N /\
      (min_lot_size_block record < 256 ^ N.of_nat 4)%N /\
      (min_lot_size_round_lot record < 256 ^ N.of_nat 4)%N /\
      (min_trade_vol record < 256 ^ N.of_nat 4)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 4)%N /\
      (decay_quantity record < 256 ^ N.of_nat 4)%N /\
      (original_contract_size record < 256 ^ N.of_nat 4)%N /\
      (second_reserved_4 record < 256 ^ N.of_nat 4)%N /\
      (trading_reference_date record < 256 ^ N.of_nat 2)%N /\
      (appl_id record < 256 ^ N.of_nat 2)%N /\
      (maturity_year record < 256 ^ N.of_nat 2)%N /\
      (decay_start_date record < 256 ^ N.of_nat 2)%N /\
      (channel record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (currency record) = 4 /\
      Datatypes.length (settl_currency record) = 4 /\
      Datatypes.length (secsubtype record) = 6 /\
      Datatypes.length (raw_symbol record) = 22 /\
      Datatypes.length (group record) = 21 /\
      Datatypes.length (exchange record) = 5 /\
      Datatypes.length (asset record) = 7 /\
      Datatypes.length (cfi record) = 7 /\
      Datatypes.length (security_type record) = 7 /\
      Datatypes.length (unit_of_measure record) = 31 /\
      Datatypes.length (underlying record) = 21 /\
      Datatypes.length (strike_price_currency record) = 4 /\
      Datatypes.length (instrument_class record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (reserved_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (match_algorithm record) = 1 /\
      (md_security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (main_fraction record < 256 ^ N.of_nat 1)%N /\
      (price_display_format record < 256 ^ N.of_nat 1)%N /\
      (settl_price_type record < 256 ^ N.of_nat 1)%N /\
      (sub_fraction record < 256 ^ N.of_nat 1)%N /\
      (underlying_product record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_update_action record) = 1 /\
      (maturity_month record < 256 ^ N.of_nat 1)%N /\
      (maturity_day record < 256 ^ N.of_nat 1)%N /\
      (maturity_week record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user_defined_instrument record) = 1 /\
      (contract_multiplier_unit record < 256 ^ N.of_nat 1)%N /\
      (flow_schedule_type record < 256 ^ N.of_nat 1)%N /\
      (tick_rule record < 256 ^ N.of_nat 1)%N /\
      (dummy_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (ts_recv record) ++
      encode_uint 8 (min_price_increment record) ++
      encode_uint 8 (display_factor record) ++
      encode_uint 8 (expiration record) ++
      encode_uint 8 (activation record) ++
      encode_uint 8 (high_limit_price record) ++
      encode_uint 8 (low_limit_price record) ++
      encode_uint 8 (max_price_variation record) ++
      encode_uint 8 (trading_reference_price record) ++
      encode_uint 8 (unit_of_measure_qty record) ++
      encode_uint 8 (min_price_increment_amount record) ++
      encode_uint 8 (price_ratio record) ++
      encode_uint 4 (inst_attrib_value record) ++
      encode_uint 4 (underlying_id record) ++
      encode_uint 4 (raw_instrument_id record) ++
      encode_uint 4 (market_depth_implied record) ++
      encode_uint 4 (market_depth record) ++
      encode_uint 4 (market_segment_id record) ++
      encode_uint 4 (max_trade_vol record) ++
      encode_uint 4 (min_lot_size record) ++
      encode_uint 4 (min_lot_size_block record) ++
      encode_uint 4 (min_lot_size_round_lot record) ++
      encode_uint 4 (min_trade_vol record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_uint 4 (contract_multiplier record) ++
      encode_uint 4 (decay_quantity record) ++
      encode_uint 4 (original_contract_size record) ++
      encode_uint 4 (second_reserved_4 record) ++
      encode_uint 2 (trading_reference_date record) ++
      encode_uint 2 (appl_id record) ++
      encode_uint 2 (maturity_year record) ++
      encode_uint 2 (decay_start_date record) ++
      encode_uint 2 (channel record) ++
      encode_bytes 4 (currency record) ++
      encode_bytes 4 (settl_currency record) ++
      encode_bytes 6 (secsubtype record) ++
      encode_bytes 22 (raw_symbol record) ++
      encode_bytes 21 (group record) ++
      encode_bytes 5 (exchange record) ++
      encode_bytes 7 (asset record) ++
      encode_bytes 7 (cfi record) ++
      encode_bytes 7 (security_type record) ++
      encode_bytes 31 (unit_of_measure record) ++
      encode_bytes 21 (underlying record) ++
      encode_bytes 4 (strike_price_currency record) ++
      encode_bytes 1 (instrument_class record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 6 (reserved_6 record) ++
      encode_bytes 1 (match_algorithm record) ++
      encode_uint 1 (md_security_trading_status record) ++
      encode_uint 1 (main_fraction record) ++
      encode_uint 1 (price_display_format record) ++
      encode_uint 1 (settl_price_type record) ++
      encode_uint 1 (sub_fraction record) ++
      encode_uint 1 (underlying_product record) ++
      encode_bytes 1 (security_update_action record) ++
      encode_uint 1 (maturity_month record) ++
      encode_uint 1 (maturity_day record) ++
      encode_uint 1 (maturity_week record) ++
      encode_bytes 1 (user_defined_instrument record) ++
      encode_uint 1 (contract_multiplier_unit record) ++
      encode_uint 1 (flow_schedule_type record) ++
      encode_uint 1 (tick_rule record) ++
      encode_uint 3 (dummy_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (ts_recv_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (min_price_increment_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (display_factor_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (expiration_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (activation_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_limit_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_limit_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (max_price_variation_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trading_reference_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (unit_of_measure_qty_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (min_price_increment_amount_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (price_ratio_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (inst_attrib_value_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (underlying_id_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (raw_instrument_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (market_depth_implied_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (market_depth_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (market_segment_id_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (max_trade_vol_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (min_lot_size_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (min_lot_size_block_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (min_lot_size_round_lot_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (min_trade_vol_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (reserved_4_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (contract_multiplier_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (decay_quantity_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (original_contract_size_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (second_reserved_4_value, bytes) =>
                                                                                                                      match decode_uint 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (trading_reference_date_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (appl_id_value, bytes) =>
                                                                                                                              match decode_uint 2 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (maturity_year_value, bytes) =>
                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (decay_start_date_value, bytes) =>
                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (channel_value, bytes) =>
                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (currency_value, bytes) =>
                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (settl_currency_value, bytes) =>
                                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (secsubtype_value, bytes) =>
                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (raw_symbol_value, bytes) =>
                                                                                                                                                          match decode_bytes 21 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (group_value, bytes) =>
                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (exchange_value, bytes) =>
                                                                                                                                                                  match decode_bytes 7 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (asset_value, bytes) =>
                                                                                                                                                                      match decode_bytes 7 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (cfi_value, bytes) =>
                                                                                                                                                                          match decode_bytes 7 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (security_type_value, bytes) =>
                                                                                                                                                                              match decode_bytes 31 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (unit_of_measure_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 21 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (underlying_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (strike_price_currency_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (instrument_class_value, bytes) =>
                                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (reserved_2_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 6 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (reserved_6_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (match_algorithm_value, bytes) =>
                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (md_security_trading_status_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (main_fraction_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (price_display_format_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (settl_price_type_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (sub_fraction_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (underlying_product_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (security_update_action_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (maturity_month_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (maturity_day_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (maturity_week_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (user_defined_instrument_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (contract_multiplier_unit_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (flow_schedule_type_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (tick_rule_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 3 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (dummy_3_value, bytes) =>
                                                                                                                                                                                                                                                                          Some ({| ts_recv := ts_recv_value; min_price_increment := min_price_increment_value; display_factor := display_factor_value; expiration := expiration_value; activation := activation_value; high_limit_price := high_limit_price_value; low_limit_price := low_limit_price_value; max_price_variation := max_price_variation_value; trading_reference_price := trading_reference_price_value; unit_of_measure_qty := unit_of_measure_qty_value; min_price_increment_amount := min_price_increment_amount_value; price_ratio := price_ratio_value; inst_attrib_value := inst_attrib_value_value; underlying_id := underlying_id_value; raw_instrument_id := raw_instrument_id_value; market_depth_implied := market_depth_implied_value; market_depth := market_depth_value; market_segment_id := market_segment_id_value; max_trade_vol := max_trade_vol_value; min_lot_size := min_lot_size_value; min_lot_size_block := min_lot_size_block_value; min_lot_size_round_lot := min_lot_size_round_lot_value; min_trade_vol := min_trade_vol_value; reserved_4 := reserved_4_value; contract_multiplier := contract_multiplier_value; decay_quantity := decay_quantity_value; original_contract_size := original_contract_size_value; second_reserved_4 := second_reserved_4_value; trading_reference_date := trading_reference_date_value; appl_id := appl_id_value; maturity_year := maturity_year_value; decay_start_date := decay_start_date_value; channel := channel_value; currency := currency_value; settl_currency := settl_currency_value; secsubtype := secsubtype_value; raw_symbol := raw_symbol_value; group := group_value; exchange := exchange_value; asset := asset_value; cfi := cfi_value; security_type := security_type_value; unit_of_measure := unit_of_measure_value; underlying := underlying_value; strike_price_currency := strike_price_currency_value; instrument_class := instrument_class_value; reserved_2 := reserved_2_value; strike_price := strike_price_value; reserved_6 := reserved_6_value; match_algorithm := match_algorithm_value; md_security_trading_status := md_security_trading_status_value; main_fraction := main_fraction_value; price_display_format := price_display_format_value; settl_price_type := settl_price_type_value; sub_fraction := sub_fraction_value; underlying_product := underlying_product_value; security_update_action := security_update_action_value; maturity_month := maturity_month_value; maturity_day := maturity_day_value; maturity_week := maturity_week_value; user_defined_instrument := user_defined_instrument_value; contract_multiplier_unit := contract_multiplier_unit_value; flow_schedule_type := flow_schedule_type_value; tick_rule := tick_rule_value; dummy_3 := dummy_3_value |}, bytes)
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 344.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 bound_64]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
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
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_bytes by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_uint by exact bound_50.
      rewrite decode_encode_uint by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_uint by exact bound_61.
      rewrite decode_encode_uint by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentDefMsg.

  Module ImbalanceMsg.

    (** An auction imbalance message; the record of the imbalance schema *)
    Record t := {
      ts_recv : N;
      ref_price : N;
      auction_time : N;
      cont_book_clr_price : N;
      auct_interest_clr_price : N;
      ssr_filling_price : N;
      ind_match_price : N;
      upper_collar : N;
      lower_collar : N;
      paired_qty : N;
      total_imbalance_qty : N;
      market_imbalance_qty : N;
      unpaired_qty : N;
      auction_type : list byte;
      side : list byte;
      auction_status : N;
      freeze_status : N;
      num_extensions : N;
      unpaired_side : list byte;
      significant_imbalance : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ts_recv record < 256 ^ N.of_nat 8)%N /\
      (ref_price record < 256 ^ N.of_nat 8)%N /\
      (auction_time record < 256 ^ N.of_nat 8)%N /\
      (cont_book_clr_price record < 256 ^ N.of_nat 8)%N /\
      (auct_interest_clr_price record < 256 ^ N.of_nat 8)%N /\
      (ssr_filling_price record < 256 ^ N.of_nat 8)%N /\
      (ind_match_price record < 256 ^ N.of_nat 8)%N /\
      (upper_collar record < 256 ^ N.of_nat 8)%N /\
      (lower_collar record < 256 ^ N.of_nat 8)%N /\
      (paired_qty record < 256 ^ N.of_nat 4)%N /\
      (total_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (market_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (unpaired_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (auction_status record < 256 ^ N.of_nat 1)%N /\
      (freeze_status record < 256 ^ N.of_nat 1)%N /\
      (num_extensions record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (unpaired_side record) = 1 /\
      Datatypes.length (significant_imbalance record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (ts_recv record) ++
      encode_uint 8 (ref_price record) ++
      encode_uint 8 (auction_time record) ++
      encode_uint 8 (cont_book_clr_price record) ++
      encode_uint 8 (auct_interest_clr_price record) ++
      encode_uint 8 (ssr_filling_price record) ++
      encode_uint 8 (ind_match_price record) ++
      encode_uint 8 (upper_collar record) ++
      encode_uint 8 (lower_collar record) ++
      encode_uint 4 (paired_qty record) ++
      encode_uint 4 (total_imbalance_qty record) ++
      encode_uint 4 (market_imbalance_qty record) ++
      encode_uint 4 (unpaired_qty record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (auction_status record) ++
      encode_uint 1 (freeze_status record) ++
      encode_uint 1 (num_extensions record) ++
      encode_bytes 1 (unpaired_side record) ++
      encode_bytes 1 (significant_imbalance record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (ts_recv_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (ref_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cont_book_clr_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (auct_interest_clr_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ssr_filling_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ind_match_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (upper_collar_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (lower_collar_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (paired_qty_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (total_imbalance_qty_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (market_imbalance_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (unpaired_qty_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (auction_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (side_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (auction_status_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (freeze_status_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (num_extensions_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (unpaired_side_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (significant_imbalance_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (reserved_1_value, bytes) =>
                                                                                          Some ({| ts_recv := ts_recv_value; ref_price := ref_price_value; auction_time := auction_time_value; cont_book_clr_price := cont_book_clr_price_value; auct_interest_clr_price := auct_interest_clr_price_value; ssr_filling_price := ssr_filling_price_value; ind_match_price := ind_match_price_value; upper_collar := upper_collar_value; lower_collar := lower_collar_value; paired_qty := paired_qty_value; total_imbalance_qty := total_imbalance_qty_value; market_imbalance_qty := market_imbalance_qty_value; unpaired_qty := unpaired_qty_value; auction_type := auction_type_value; side := side_value; auction_status := auction_status_value; freeze_status := freeze_status_value; num_extensions := num_extensions_value; unpaired_side := unpaired_side_value; significant_imbalance := significant_imbalance_value; reserved_1 := reserved_1_value |}, bytes)
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 96.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ImbalanceMsg.

  Module ErrorMsg.

    (** An error message from the Databento Live Subscription Gateway (LSG) *)
    Record t := {
      err : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (err record) = 64.

    Definition encode (record : t) : list byte :=
      encode_bytes 64 (err record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 64 bytes with
      | None => None
      | Some (err_value, bytes) =>
          Some ({| err := err_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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

  End ErrorMsg.

  Module SymbolMappingMsg.

    (** A symbol mapping message, which maps a symbol of one SType to another *)
    Record t := {
      stype_in_symbol : list byte;
      stype_out_symbol : list byte;
      dummy_4 : N;
      start_ts : N;
      end_ts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stype_in_symbol record) = 22 /\
      Datatypes.length (stype_out_symbol record) = 22 /\
      (dummy_4 record < 256 ^ N.of_nat 4)%N /\
      (start_ts record < 256 ^ N.of_nat 8)%N /\
      (end_ts record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 22 (stype_in_symbol record) ++
      encode_bytes 22 (stype_out_symbol record) ++
      encode_uint 4 (dummy_4 record) ++
      encode_uint 8 (start_ts record) ++
      encode_uint 8 (end_ts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 22 bytes with
      | None => None
      | Some (stype_in_symbol_value, bytes) =>
          match decode_bytes 22 bytes with
          | None => None
          | Some (stype_out_symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (dummy_4_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (start_ts_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (end_ts_value, bytes) =>
                          Some ({| stype_in_symbol := stype_in_symbol_value; stype_out_symbol := stype_out_symbol_value; dummy_4 := dummy_4_value; start_ts := start_ts_value; end_ts := end_ts_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolMappingMsg.

  Module SystemMsg.

    (** A non-error message from the Databento Live Subscription Gateway (LSG); also used for heartbeating *)
    Record t := {
      msg : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (msg record) = 64.

    Definition encode (record : t) : list byte :=
      encode_bytes 64 (msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 64 bytes with
      | None => None
      | Some (msg_value, bytes) =>
          Some ({| msg := msg_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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

  End SystemMsg.

  Module StatMsg.

    (** A statistics message; the record of the statistics schema *)
    Record t := {
      ts_recv : N;
      ts_ref : N;
      price : N;
      quantity : N;
      sequence : N;
      ts_in_delta : N;
      stat_type : N;
      channel : N;
      update_action : N;
      stat_flags : N;
      reserved_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ts_recv record < 256 ^ N.of_nat 8)%N /\
      (ts_ref record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N /\
      (ts_in_delta record < 256 ^ N.of_nat 4)%N /\
      (stat_type record < 256 ^ N.of_nat 2)%N /\
      (channel record < 256 ^ N.of_nat 2)%N /\
      (update_action record < 256 ^ N.of_nat 1)%N /\
      (stat_flags record < 256 ^ N.of_nat 1)%N /\
      (reserved_6 record < 256 ^ N.of_nat 6)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (ts_recv record) ++
      encode_uint 8 (ts_ref record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (sequence record) ++
      encode_uint 4 (ts_in_delta record) ++
      encode_uint 2 (stat_type record) ++
      encode_uint 2 (channel record) ++
      encode_uint 1 (update_action record) ++
      encode_uint 1 (stat_flags record) ++
      encode_uint 6 (reserved_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (ts_recv_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (ts_ref_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sequence_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ts_in_delta_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (stat_type_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (channel_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (update_action_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (stat_flags_value, bytes) =>
                                              match decode_uint 6 bytes with
                                              | None => None
                                              | Some (reserved_6_value, bytes) =>
                                                  Some ({| ts_recv := ts_recv_value; ts_ref := ts_ref_value; price := price_value; quantity := quantity_value; sequence := sequence_value; ts_in_delta := ts_in_delta_value; stat_type := stat_type_value; channel := channel_value; update_action := update_action_value; stat_flags := stat_flags_value; reserved_6 := reserved_6_value |}, bytes)
                                              end
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StatMsg.

  Module ConsolidatedBidAskPair.

    (** A price level consolidated from multiple venues *)
    Record t := {
      bid_px : N;
      ask_px : N;
      bid_sz : N;
      ask_sz : N;
      bid_pb : N;
      reserved_2 : N;
      ask_pb : N;
      second_reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (bid_px record < 256 ^ N.of_nat 8)%N /\
      (ask_px record < 256 ^ N.of_nat 8)%N /\
      (bid_sz record < 256 ^ N.of_nat 4)%N /\
      (ask_sz record < 256 ^ N.of_nat 4)%N /\
      (bid_pb record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (ask_pb record < 256 ^ N.of_nat 2)%N /\
      (second_reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (bid_px record) ++
      encode_uint 8 (ask_px record) ++
      encode_uint 4 (bid_sz record) ++
      encode_uint 4 (ask_sz record) ++
      encode_uint 2 (bid_pb record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 2 (ask_pb record) ++
      encode_uint 2 (second_reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (bid_px_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (ask_px_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_sz_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_sz_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (bid_pb_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_2_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_pb_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (second_reserved_2_value, bytes) =>
                                      Some ({| bid_px := bid_px_value; ask_px := ask_px_value; bid_sz := bid_sz_value; ask_sz := ask_sz_value; bid_pb := bid_pb_value; reserved_2 := reserved_2_value; ask_pb := ask_pb_value; second_reserved_2 := second_reserved_2_value |}, bytes)
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

  End ConsolidatedBidAskPair.

  Module ConsolidatedBidAskPair2.

    (** A price level consolidated from multiple venues *)
    Record t := {
      bid_px : N;
      ask_px : N;
      bid_sz : N;
      ask_sz : N;
      bid_pb : N;
      reserved_2 : N;
      ask_pb : N;
      second_reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (bid_px record < 256 ^ N.of_nat 8)%N /\
      (ask_px record < 256 ^ N.of_nat 8)%N /\
      (bid_sz record < 256 ^ N.of_nat 4)%N /\
      (ask_sz record < 256 ^ N.of_nat 4)%N /\
      (bid_pb record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (ask_pb record < 256 ^ N.of_nat 2)%N /\
      (second_reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (bid_px record) ++
      encode_uint 8 (ask_px record) ++
      encode_uint 4 (bid_sz record) ++
      encode_uint 4 (ask_sz record) ++
      encode_uint 2 (bid_pb record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 2 (ask_pb record) ++
      encode_uint 2 (second_reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (bid_px_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (ask_px_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_sz_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_sz_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (bid_pb_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (reserved_2_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_pb_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (second_reserved_2_value, bytes) =>
                                      Some ({| bid_px := bid_px_value; ask_px := ask_px_value; bid_sz := bid_sz_value; ask_sz := ask_sz_value; bid_pb := bid_pb_value; reserved_2 := reserved_2_value; ask_pb := ask_pb_value; second_reserved_2 := second_reserved_2_value |}, bytes)
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

  End ConsolidatedBidAskPair2.

  Module BidAskPair2.

    (** A level *)
    Record t := {
      bid_px : N;
      ask_px : N;
      bid_sz : N;
      ask_sz : N;
      bid_ct : N;
      ask_ct : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (bid_px record < 256 ^ N.of_nat 8)%N /\
      (ask_px record < 256 ^ N.of_nat 8)%N /\
      (bid_sz record < 256 ^ N.of_nat 4)%N /\
      (ask_sz record < 256 ^ N.of_nat 4)%N /\
      (bid_ct record < 256 ^ N.of_nat 4)%N /\
      (ask_ct record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (bid_px record) ++
      encode_uint 8 (ask_px record) ++
      encode_uint 4 (bid_sz record) ++
      encode_uint 4 (ask_sz record) ++
      encode_uint 4 (bid_ct record) ++
      encode_uint 4 (ask_ct record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (bid_px_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (ask_px_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_sz_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_sz_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_ct_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ask_ct_value, bytes) =>
                              Some ({| bid_px := bid_px_value; ask_px := ask_px_value; bid_sz := bid_sz_value; ask_sz := ask_sz_value; bid_ct := bid_ct_value; ask_ct := ask_ct_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BidAskPair2.

End DatabentoMarketDataNormalizedV1GatewayStream.
