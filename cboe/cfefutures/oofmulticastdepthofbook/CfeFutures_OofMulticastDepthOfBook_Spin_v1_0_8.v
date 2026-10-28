From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange OOF Multicast Depth Of Book

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
      - a Reassemble rule
      - a run filling what frames it
      - a run counted by a field
      - a field read in bits
  *)

Module CfeFuturesOofMulticastDepthOfBookV108.

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

    (** The Time Reference message is used to provide a midnight reference point for recipients of the feed. It is sent whenever the system starts up and when the system crosses a midnight boundary. All subsequent Time messages for the same unit will the use the last Midnight Reference until another Time Reference message is received for that unit. The Time Reference message includes the Trade Date, so most other sequenced messages will not include that information. Time Reference messages will be included in a spin response. *)
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

    (** A Time message is immediately generated and sent when there is a PITCH event for a given clock second. If there is no PITCH event for a given clock second, then no Time message is sent for that second. All subsequent Time Offset fields for the same unit will use the new Time message value as the base until another Time message is received for the same unit. The Time field is the number of seconds relative to midnight Central Time, which is provided in the Time Reference message. The Time message also includes the Epoch Time field, which is the current time represented as the number of whole seconds since the Epoch (Midnight January 1, 1970). *)
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

  Module OofSymbolMappingMessage.

    (** An OOF Symbol Mapping message is used to map the 6 character multicast feed symbol field and options on futures name to the option contract and future underlying. The option contract is comprised of the strike price, put/call flag, options expiration date, and future underlying. The future underlying is comprised of the futures product and futures expiration date, which map to a futures symbol. This message can be sent either as a sequenced message or as an unsequenced message. It is sent as a sequenced message at system startup upon the beginning of a trading session or if an instrument is created or modified during a trading day. A new sequenced message may also be sent for a symbol that does not visibly change any attribute. A continuous loop of unsequenced symbol mapping messages (sequence = 0) is sent throughout the day at variable rates as bandwidth allows. The Time Offset field should be ignored on unsequenced messages. OOF Symbol Mapping messages are included in a spin response and will be disseminated before Complex Instrument Definition Expanded messages. *)
    Record t := {
      time_offset : N;
      feed_symbol : list byte;
      futures_product : list byte;
      futures_expiration : N;
      futures_symbol : list byte;
      strike_price : N;
      call_put_indicator : list byte;
      options_expiration : N;
      options_on_futures_name : list byte;
      symbol_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (feed_symbol record) = 6 /\
      Datatypes.length (futures_product record) = 8 /\
      (futures_expiration record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (futures_symbol record) = 6 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (call_put_indicator record) = 1 /\
      (options_expiration record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (options_on_futures_name record) = 16 /\
      Datatypes.length (symbol_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (feed_symbol record) ++
      encode_bytes 8 (futures_product record) ++
      encode_uint 4 (futures_expiration record) ++
      encode_bytes 6 (futures_symbol record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (call_put_indicator record) ++
      encode_uint 4 (options_expiration record) ++
      encode_bytes 16 (options_on_futures_name record) ++
      encode_bytes 1 (symbol_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (feed_symbol_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (futures_product_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (futures_expiration_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (futures_symbol_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (call_put_indicator_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (options_expiration_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (options_on_futures_name_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (symbol_condition_value, bytes) =>
                                              Some ({| time_offset := time_offset_value; feed_symbol := feed_symbol_value; futures_product := futures_product_value; futures_expiration := futures_expiration_value; futures_symbol := futures_symbol_value; strike_price := strike_price_value; call_put_indicator := call_put_indicator_value; options_expiration := options_expiration_value; options_on_futures_name := options_on_futures_name_value; symbol_condition := symbol_condition_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OofSymbolMappingMessage.

  Module TradingStatusMessage.

    (** The Trading Status message is used to indicate the current trading status of a symbol. A Trading Status message will be sent for all symbols as they transition through various trading states. If a Trading Status message has not been received for a symbol, then the Trading Status for the symbol should be assumed to be H = Halted. The following summarizes the Trading Status values for options in the CFE system: H = Halted state. This state is used for Supervisory Halts initiated by the Trade Desk. Orders are not being accepted in this state. Q = Queuing state. This state is used when orders are being accepted for queuing. The Queuing state is used during the pre-open for all symbols. It is also used for spread instruments that may not be tradeable due to Threshold Width. T = Trading state. This state is used when the symbol is available for trading. CFE will send a Trading Status of Q once orders can be accepted for queuing in preparation for the open. At or after the opening time, CFE will send a Trading Status of T as symbols are opened for trading. Once trading is done for the day CFE will send a Trading Status of H indicating the symbol is Halted. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      reserved_2 : N;
      trading_status : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (reserved_2_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_uint 3 bytes with
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module AddOrderLongMessage.

    (** An Add Order message represents a newly accepted visible order on the CFE book. It includes a day- specific Order Id assigned by CFE to the order. *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      quantity_long : N;
      symbol : list byte;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (quantity_long record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_long_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_long := quantity_long_value; symbol := symbol_value; price_long := price_long_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderLongMessage.

  Module AddOrderShortMessage.

    (** An Add Order message represents a newly accepted visible order on the CFE book. It includes a day- specific Order Id assigned by CFE to the order. *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      quantity_short : N;
      symbol : list byte;
      price_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 2 (quantity_short record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 2 (price_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (quantity_short_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (price_short_value, bytes) =>
                              Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_short := quantity_short_value; symbol := symbol_value; price_short := price_short_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderShortMessage.

  Module SettlementMessage.

    (** Settlement messages are used to provide information concerning indicative, approved, or corrected daily and final settlement prices for CFE products. An indicative daily settlement price (Issue = I) is calculated by the system and sent immediately after an instrument closes trading but before the settlement price is approved. An approved settlement price (Issue = S) is sent once the CFE Trade Desk approves a settlement price for an instrument. If there is an error in the approved settlement price, then it may be re-issued (Issue = R). *)
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

  Module LoginMessage.

    (** The Login message is the first message sent to the GRP by a user's process after the connection to the GRP is established. Failure to login before sending any other message type will result in the connection being dropped by the GRP. *)
    Record t := {
      session_sub_id : list byte;
      username : list byte;
      filler : list byte;
      password : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_sub_id record) = 4 /\
      Datatypes.length (username record) = 4 /\
      Datatypes.length (filler record) = 2 /\
      Datatypes.length (password record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (session_sub_id record) ++
      encode_bytes 4 (username record) ++
      encode_bytes 2 (filler record) ++
      encode_bytes 10 (password record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (session_sub_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (username_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (password_value, bytes) =>
                      Some ({| session_sub_id := session_sub_id_value; username := username_value; filler := filler_value; password := password_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginMessage.

  Module LoginResponseMessage.

    (** The Login Response message is sent by the GRP to a user's process in response to a Login message. The status field is used to reflect an accepted login or the reason the session was not accepted. If login fails, the connection will be dropped after the Login Response message is sent. *)
    Record t := {
      login_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_response_status_value, bytes) =>
          Some ({| login_response_status := login_response_status_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End LoginResponseMessage.

  Module SpinImageAvailableMessage.

    (** The Spin Image Available message is sent once per second and indicates through what sequence number a spin is available. *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End SpinImageAvailableMessage.

  Module SpinRequestMessage.

    (** The Spin Request message is used by a user's process to request transmission of a spin of the unit's order book. Refer to Spin Servers for more complete details regarding Sequence specification as well as buffering requirements. *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End SpinRequestMessage.

  Module SpinResponseMessage.

    (** The Spin Response message is sent in response to a user's Spin Request message indicating whether a spin will be sent. *)
    Record t := {
      sequence : N;
      order_count : N;
      spin_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (spin_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record) ++
      encode_uint 4 (order_count record) ++
      encode_bytes 1 (spin_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (spin_response_status_value, bytes) =>
                  Some ({| sequence := sequence_value; order_count := order_count_value; spin_response_status := spin_response_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SpinResponseMessage.

  Module SpinFinishedMessage.

    (** The Spin Finished message is sent to indicate that all messages for the spin requested have been sent. A Spin Finished message is only sent if a Spin Request message was not rejected. Upon receipt of a Spin Finished message, any buffered multicast messages should be applied to the participant's copy of the book to make it current. *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End SpinFinishedMessage.

  Module InstrumentDefinitionRequestMessage.

    (** The Instrument Definition Request message is used to request transmission of this unit's OOF Symbol Mappings and Complex Instrument Definitions. All OOF Symbol Mapping messages will be sent before Complex Instrument Definition Expanded messages. Refer to Spin Servers for more complete details regarding Sequence specification as well as buffering requirements. *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End InstrumentDefinitionRequestMessage.

  Module InstrumentDefinitionResponseMessage.

    (** The Instrument Definition Response message is sent in response to a user's Instrument Definition Request message indicating whether a spin will be sent. *)
    Record t := {
      sequence : N;
      instrument_count : N;
      instrument_definition_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N /\
      (instrument_count record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument_definition_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record) ++
      encode_uint 4 (instrument_count record) ++
      encode_bytes 1 (instrument_definition_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (instrument_definition_response_status_value, bytes) =>
                  Some ({| sequence := sequence_value; instrument_count := instrument_count_value; instrument_definition_response_status := instrument_definition_response_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End InstrumentDefinitionResponseMessage.

End CfeFuturesOofMulticastDepthOfBookV108.
