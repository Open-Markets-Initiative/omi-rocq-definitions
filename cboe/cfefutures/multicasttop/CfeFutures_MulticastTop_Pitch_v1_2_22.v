From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Futures Multicast Top

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
      - the dispatch that chooses a message by its type
      - a run filling what frames it
      - a field read in bits
      - a run counted by a field
  *)

Module CfeFuturesMulticastTopV1222.

  Module PacketHeader.

    Record t := {
      length_ : N;
      message_count : N;
      unit_ : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (unit_ record < 256 ^ N.of_nat 1)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (unit_ record) ++
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (unit__value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; unit_ := unit__value; sequence := sequence_value |}, bytes)
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 1)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module TimeReferenceMessage.

    (** The Time Reference message is used to provide a midnight reference point for recipients of the feed. It is sent whenever the system starts up and when the system crosses a midnight boundary. *)
    Record t := {
      midnight_reference : N;
      time_reference : N;
      time_offset : N;
      trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (midnight_reference record < 256 ^ N.of_nat 4)%N /\
      (time_reference record < 256 ^ N.of_nat 4)%N /\
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (midnight_reference record) ++
      encode_uint 4 (time_reference record) ++
      encode_uint 4 (time_offset record) ++
      encode_uint 4 (trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (midnight_reference_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (time_reference_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (time_offset_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_date_value, bytes) =>
                      Some ({| midnight_reference := midnight_reference_value; time_reference := time_reference_value; time_offset := time_offset_value; trade_date := trade_date_value |}, bytes)
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

  End TimeReferenceMessage.

  Module TimeMessage.

    (** A Time message is immediately generated and sent when there is a TOP event for a given clock second. *)
    Record t := {
      time_reference : N;
      epoch_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_reference record < 256 ^ N.of_nat 4)%N /\
      (epoch_time record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_reference record) ++
      encode_uint 4 (epoch_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_reference_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (epoch_time_value, bytes) =>
              Some ({| time_reference := time_reference_value; epoch_time := epoch_time_value |}, bytes)
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

  End TimeMessage.

  Module UnitClearMessage.

    (** The Unit Clear message instructs feed recipients to clear all market snapshots for the CFE book in the unit specified in the Sequenced Unit Header message header. *)
    Record t := {
      time_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          Some ({| time_offset := time_offset_value |}, bytes)
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

  End UnitClearMessage.

  Module FuturesVarianceSymbolMappingMessage.

    (** The Futures Variance Symbol Mapping message is used to disseminate symbol reference data for S&P 500 Variance Futures (VA Futures) symbols. *)
    Record t := {
      time_offset : N;
      unit_timestamp : N;
      feed_symbol : list byte;
      futures_symbol : list byte;
      accrued_day_variance : N;
      num_final_returns : N;
      num_elapsed_returns : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (unit_timestamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (feed_symbol record) = 6 /\
      Datatypes.length (futures_symbol record) = 12 /\
      (accrued_day_variance record < 256 ^ N.of_nat 8)%N /\
      (num_final_returns record < 256 ^ N.of_nat 2)%N /\
      (num_elapsed_returns record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 4 (unit_timestamp record) ++
      encode_bytes 6 (feed_symbol record) ++
      encode_bytes 12 (futures_symbol record) ++
      encode_uint 8 (accrued_day_variance record) ++
      encode_uint 2 (num_final_returns record) ++
      encode_uint 2 (num_elapsed_returns record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (unit_timestamp_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (feed_symbol_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (futures_symbol_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (accrued_day_variance_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (num_final_returns_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (num_elapsed_returns_value, bytes) =>
                                  Some ({| time_offset := time_offset_value; unit_timestamp := unit_timestamp_value; feed_symbol := feed_symbol_value; futures_symbol := futures_symbol_value; accrued_day_variance := accrued_day_variance_value; num_final_returns := num_final_returns_value; num_elapsed_returns := num_elapsed_returns_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FuturesVarianceSymbolMappingMessage.

  Module PriceLimitsMessage.

    (** The Price Limits message can be sent as a sequenced or un-sequenced message. It is sent out at the start of the session for products subject to price limits per the contract specifications. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      upper_price_limit : N;
      lower_price_limit : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (upper_price_limit record < 256 ^ N.of_nat 8)%N /\
      (lower_price_limit record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (upper_price_limit record) ++
      encode_uint 8 (lower_price_limit record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (upper_price_limit_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (lower_price_limit_value, bytes) =>
                      Some ({| time_offset := time_offset_value; symbol := symbol_value; upper_price_limit := upper_price_limit_value; lower_price_limit := lower_price_limit_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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

  End PriceLimitsMessage.

  Module MarketSnapshotShortMessage.

    (** A Market Snapshot message provides a snapshot of the price and size for the bid and ask, last trade price, total number of contracts traded, and the current trading status of a single symbol. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      unit_timestamp : N;
      bid_price_short : N;
      bid_quantity_short : N;
      ask_price_short : N;
      ask_quantity_short : N;
      last_trade_price_short : N;
      last_trade_size_short : N;
      last_trade_condition : list byte;
      total_volume : N;
      trading_status : list byte;
      reserved_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (unit_timestamp record < 256 ^ N.of_nat 4)%N /\
      (bid_price_short record < 256 ^ N.of_nat 2)%N /\
      (bid_quantity_short record < 256 ^ N.of_nat 2)%N /\
      (ask_price_short record < 256 ^ N.of_nat 2)%N /\
      (ask_quantity_short record < 256 ^ N.of_nat 2)%N /\
      (last_trade_price_short record < 256 ^ N.of_nat 2)%N /\
      (last_trade_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (last_trade_condition record) = 1 /\
      (total_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (reserved_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (unit_timestamp record) ++
      encode_uint 2 (bid_price_short record) ++
      encode_uint 2 (bid_quantity_short record) ++
      encode_uint 2 (ask_price_short record) ++
      encode_uint 2 (ask_quantity_short record) ++
      encode_uint 2 (last_trade_price_short record) ++
      encode_uint 2 (last_trade_size_short record) ++
      encode_bytes 1 (last_trade_condition record) ++
      encode_uint 4 (total_volume record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (unit_timestamp_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_price_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (bid_quantity_short_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ask_price_short_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_quantity_short_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (last_trade_price_short_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (last_trade_size_short_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (last_trade_condition_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (total_volume_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trading_status_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (reserved_3_value, bytes) =>
                                                          Some ({| time_offset := time_offset_value; symbol := symbol_value; unit_timestamp := unit_timestamp_value; bid_price_short := bid_price_short_value; bid_quantity_short := bid_quantity_short_value; ask_price_short := ask_price_short_value; ask_quantity_short := ask_quantity_short_value; last_trade_price_short := last_trade_price_short_value; last_trade_size_short := last_trade_size_short_value; last_trade_condition := last_trade_condition_value; total_volume := total_volume_value; trading_status := trading_status_value; reserved_3 := reserved_3_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSnapshotShortMessage.

  Module MarketSnapshotLongMessage.

    (** A Market Snapshot message provides a snapshot of the price and size for the bid and ask, last trade price, total number of contracts traded, and the current trading status of a single symbol. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      unit_timestamp : N;
      bid_price_long : N;
      bid_quantity_long : N;
      ask_price_long : N;
      ask_quantity_long : N;
      last_trade_price_long : N;
      last_trade_size_long : N;
      last_trade_condition : list byte;
      total_volume : N;
      trading_status : list byte;
      reserved_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (unit_timestamp record < 256 ^ N.of_nat 4)%N /\
      (bid_price_long record < 256 ^ N.of_nat 8)%N /\
      (bid_quantity_long record < 256 ^ N.of_nat 4)%N /\
      (ask_price_long record < 256 ^ N.of_nat 8)%N /\
      (ask_quantity_long record < 256 ^ N.of_nat 4)%N /\
      (last_trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (last_trade_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_trade_condition record) = 1 /\
      (total_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (reserved_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (unit_timestamp record) ++
      encode_uint 8 (bid_price_long record) ++
      encode_uint 4 (bid_quantity_long record) ++
      encode_uint 8 (ask_price_long record) ++
      encode_uint 4 (ask_quantity_long record) ++
      encode_uint 8 (last_trade_price_long record) ++
      encode_uint 4 (last_trade_size_long record) ++
      encode_bytes 1 (last_trade_condition record) ++
      encode_uint 4 (total_volume record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (unit_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_quantity_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ask_price_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (ask_quantity_long_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_trade_price_long_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_trade_size_long_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (last_trade_condition_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (total_volume_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trading_status_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (reserved_3_value, bytes) =>
                                                          Some ({| time_offset := time_offset_value; symbol := symbol_value; unit_timestamp := unit_timestamp_value; bid_price_long := bid_price_long_value; bid_quantity_long := bid_quantity_long_value; ask_price_long := ask_price_long_value; ask_quantity_long := ask_quantity_long_value; last_trade_price_long := last_trade_price_long_value; last_trade_size_long := last_trade_size_long_value; last_trade_condition := last_trade_condition_value; total_volume := total_volume_value; trading_status := trading_status_value; reserved_3 := reserved_3_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSnapshotLongMessage.

  Module SingleSideUpdateShortMessage.

    (** Single Side Update messages provide an updated price and size for a single side of a Symbol. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      side : list byte;
      price_short : N;
      quantity_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (side record) = 1 /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (quantity_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (side record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 2 (quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (price_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (quantity_short_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol := symbol_value; side := side_value; price_short := price_short_value; quantity_short := quantity_short_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideUpdateShortMessage.

  Module SingleSideUpdateLongMessage.

    (** Single Side Update messages provide an updated price and size for a single side of a Symbol. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      side : list byte;
      price_long : N;
      quantity_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (side record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (quantity_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 4 (quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_long_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol := symbol_value; side := side_value; price_long := price_long_value; quantity_long := quantity_long_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideUpdateLongMessage.

  Module TwoSideUpdateShortMessage.

    (** Two Side Update messages provide an updated price and size for both sides of a Symbol. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      bid_price_short : N;
      bid_quantity_short : N;
      ask_price_short : N;
      ask_quantity_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (bid_price_short record < 256 ^ N.of_nat 2)%N /\
      (bid_quantity_short record < 256 ^ N.of_nat 2)%N /\
      (ask_price_short record < 256 ^ N.of_nat 2)%N /\
      (ask_quantity_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 2 (bid_price_short record) ++
      encode_uint 2 (bid_quantity_short record) ++
      encode_uint 2 (ask_price_short record) ++
      encode_uint 2 (ask_quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (bid_price_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_quantity_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (ask_price_short_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (ask_quantity_short_value, bytes) =>
                              Some ({| time_offset := time_offset_value; symbol := symbol_value; bid_price_short := bid_price_short_value; bid_quantity_short := bid_quantity_short_value; ask_price_short := ask_price_short_value; ask_quantity_short := ask_quantity_short_value |}, bytes)
                          end
                      end
                  end
              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TwoSideUpdateShortMessage.

  Module TwoSideUpdateLongMessage.

    (** Two Side Update messages provide an updated price and size for both sides of a Symbol. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      bid_price_long : N;
      bid_quantity_long : N;
      ask_price_long : N;
      ask_quantity_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (bid_price_long record < 256 ^ N.of_nat 8)%N /\
      (bid_quantity_long record < 256 ^ N.of_nat 4)%N /\
      (ask_price_long record < 256 ^ N.of_nat 8)%N /\
      (ask_quantity_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (bid_price_long record) ++
      encode_uint 4 (bid_quantity_long record) ++
      encode_uint 8 (ask_price_long record) ++
      encode_uint 4 (ask_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_price_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (bid_quantity_long_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (ask_price_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ask_quantity_long_value, bytes) =>
                              Some ({| time_offset := time_offset_value; symbol := symbol_value; bid_price_long := bid_price_long_value; bid_quantity_long := bid_quantity_long_value; ask_price_long := ask_price_long_value; ask_quantity_long := ask_quantity_long_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TwoSideUpdateLongMessage.

  Module TopTradeMessage.

    (** The TOP Trade message provides information about executions of orders on the CFE book. TOP Trade messages are necessary to calculate CFE execution-based data. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      quantity_long : N;
      price_long : N;
      execution_id : N;
      total_volume : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (quantity_long record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (quantity_long record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (execution_id record) ++
      encode_uint 4 (total_volume record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (execution_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_condition_value, bytes) =>
                                  Some ({| time_offset := time_offset_value; symbol := symbol_value; quantity_long := quantity_long_value; price_long := price_long_value; execution_id := execution_id_value; total_volume := total_volume_value; trade_condition := trade_condition_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TopTradeMessage.

  Module SettlementMessage.

    (** Settlement messages are used to provide information concerning indicative, approved, or corrected daily and final settlement prices for CFE products. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      trade_date : N;
      settlement_price : N;
      issue : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issue record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (trade_date record) ++
      encode_uint 8 (settlement_price record) ++
      encode_bytes 1 (issue record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_date_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (settlement_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (issue_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol := symbol_value; trade_date := trade_date_value; settlement_price := settlement_price_value; issue := issue_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementMessage.

  Module TradingStatusMessage.

    (** The Trading Status message is used to indicate the current trading status of a Futures contract. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      reserved_2 : list byte;
      trading_status : list byte;
      reserved_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (reserved_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (reserved_2_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (reserved_3_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol := symbol_value; reserved_2 := reserved_2_value; trading_status := trading_status_value; reserved_3 := reserved_3_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module OpenInterestMessage.

    (** The Open Interest message is sent to communicate a symbol's open interest, usually for the prior trading date. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      trade_date : N;
      open_interest : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (trade_date record) ++
      encode_uint 4 (open_interest record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (open_interest_value, bytes) =>
                      Some ({| time_offset := time_offset_value; symbol := symbol_value; trade_date := trade_date_value; open_interest := open_interest_value |}, bytes)
                  end
              end
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

  End OpenInterestMessage.

  Module EndOfSessionMessage.

    (** The End of Session message is sent for each unit when the unit shuts down. No more sequenced messages will be delivered for this unit, but heartbeats from the unit may be received. *)
    Record t := {
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          Some ({| timestamp := timestamp_value |}, bytes)
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

  End EndOfSessionMessage.

End CfeFuturesMulticastTopV1222.
