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
      - the dispatch that chooses a message by its type
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

  Module UnitClearMessage.

    (** The Unit Clear message instructs feed recipients to clear all orders for the CFE book in the unit specified in the Sequenced Unit Header message header. It would be distributed in rare recovery events such as a data center fail-over. *)
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

  Module TransactionBeginMessage.

    (** The Transaction Begin message indicates any subsequent messages, up to the accompanying Transaction End message, are all part of the same transaction block. One example of where this might be used is when a single aggressive order executes against several resting orders. All PITCH messages corresponding to such an event would be included between a Transaction Begin message and Transaction End message. It is important to note that any PITCH Message Type may be included in a transaction block and there is no guarantee that the messages apply to the same price level or even the same Symbol. Transaction Begin messages do not alter the book and can be ignored if messages are being used solely to build a book. Feed processors can use a transaction block as a trigger to postpone publishing a quote update until the end of the transaction block. In the prior example of a single aggressive order executing against multiple resting orders, a top of book feed would be able to publish a single trade message and quote update resulting from multiple Order Executed messages once it finished processing all of the messages within the transaction block. *)
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

  End TransactionBeginMessage.

  Module TransactionEndMessage.

    (** The Transaction End message indicates that a transaction indicated by a previous Transaction Begin message has completed. Transaction End messages do not alter the book and can be ignored if messages are being used solely to build a book. *)
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

  End TransactionEndMessage.

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

  Module OrderExecutedMessage.

    (** Order Executed messages are sent when an order on the CFE book is executed in whole or in part. The execution price equals the limit order price found in the original Add Order message or the limit order price in the latest Modify Order message referencing the Order Id. *)
    Record t := {
      time_offset : N;
      order_id : N;
      executed_quantity : N;
      execution_id : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (execution_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (trade_condition_value, bytes) =>
                          Some ({| time_offset := time_offset_value; order_id := order_id_value; executed_quantity := executed_quantity_value; execution_id := execution_id_value; trade_condition := trade_condition_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module ReduceSizeLongMessage.

    (** Reduce Size messages are sent when a visible order on the CFE book is partially reduced. *)
    Record t := {
      time_offset : N;
      order_id : N;
      canceled_quantity_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (canceled_quantity_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (canceled_quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (canceled_quantity_long_value, bytes) =>
                  Some ({| time_offset := time_offset_value; order_id := order_id_value; canceled_quantity_long := canceled_quantity_long_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ReduceSizeLongMessage.

  Module ReduceSizeShortMessage.

    (** Reduce Size messages are sent when a visible order on the CFE book is partially reduced. *)
    Record t := {
      time_offset : N;
      order_id : N;
      canceled_quantity_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (canceled_quantity_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (canceled_quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (canceled_quantity_short_value, bytes) =>
                  Some ({| time_offset := time_offset_value; order_id := order_id_value; canceled_quantity_short := canceled_quantity_short_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ReduceSizeShortMessage.

  Module ModifyOrderLongMessage.

    (** The Modify Order message is sent whenever an open order is visibly modified. The Order Id refers to the Order Id of the original Add Order message. Note that Modify Order messages that appear to be "no ops" (i.e. they do not appear to modify any relevant fields) will still lose priority. *)
    Record t := {
      time_offset : N;
      order_id : N;
      quantity_long : N;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_long record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity_long record) ++
      encode_uint 8 (price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      Some ({| time_offset := time_offset_value; order_id := order_id_value; quantity_long := quantity_long_value; price_long := price_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End ModifyOrderLongMessage.

  Module ModifyOrderShortMessage.

    (** The Modify Order message is sent whenever an open order is visibly modified. The Order Id refers to the Order Id of the original Add Order message. Note that Modify Order messages that appear to be "no ops" (i.e. they do not appear to modify any relevant fields) will still lose priority. *)
    Record t := {
      time_offset : N;
      order_id : N;
      quantity_short : N;
      price_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_short record < 256 ^ N.of_nat 2)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (quantity_short record) ++
      encode_uint 2 (price_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (quantity_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (price_short_value, bytes) =>
                      Some ({| time_offset := time_offset_value; order_id := order_id_value; quantity_short := quantity_short_value; price_short := price_short_value |}, bytes)
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

  End ModifyOrderShortMessage.

  Module DeleteOrderMessage.

    (** The Delete Order message is sent whenever a booked order is cancelled or leaves the order book. The Order Id refers to the Order Id of the original Add Order message. An order that is deleted from the book may return to the book later under certain circumstances. Therefore, a Delete Order message does not indicate that a given Order Id will not be sent again on a subsequent Add Order message. *)
    Record t := {
      time_offset : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              Some ({| time_offset := time_offset_value; order_id := order_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End DeleteOrderMessage.

  Module TradeLongMessage.

    (** The Trade message provides information about executions that occur off of the CFE book (such as Block trades). Trade messages are necessary to calculate CFE execution data. Trade messages do not alter the book and can be ignored if messages are being used solely to build a book. The Order Id sent in a Trade message is obfuscated and will not tie back to any real Order Id sent back via a FIX or BOE order entry session. *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      quantity_long : N;
      symbol : list byte;
      price_long : N;
      execution_id : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (quantity_long record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 1 (trade_condition record).

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
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_condition_value, bytes) =>
                                      Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_long := quantity_long_value; symbol := symbol_value; price_long := price_long_value; execution_id := execution_id_value; trade_condition := trade_condition_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeLongMessage.

  Module TradeShortMessage.

    (** The Trade message provides information about executions that occur off of the CFE book (such as Block trades). Trade messages are necessary to calculate CFE execution data. Trade messages do not alter the book and can be ignored if messages are being used solely to build a book. The Order Id sent in a Trade message is obfuscated and will not tie back to any real Order Id sent back via a FIX or BOE order entry session. *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      quantity_short : N;
      symbol : list byte;
      price_short : N;
      execution_id : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 2 (quantity_short record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 1 (trade_condition record).

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
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_condition_value, bytes) =>
                                      Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_short := quantity_short_value; symbol := symbol_value; price_short := price_short_value; execution_id := execution_id_value; trade_condition := trade_condition_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeShortMessage.

  Module TradeBreakMessage.

    (** The Trade Break message is sent whenever an execution on CFE is broken. Trade breaks are rare and only affect applications that rely upon CFE execution-based data. A Trade Break message followed immediately be a new Trade message with the same Execution Id indicates that a trade correction has occurred. Applications that simply build a CFE book can ignore Trade Break messages. *)
    Record t := {
      time_offset : N;
      execution_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (execution_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (execution_id_value, bytes) =>
              Some ({| time_offset := time_offset_value; execution_id := execution_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End TradeBreakMessage.

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

  Module EndOfSessionMessage.

    (** The End of Session message is sent for each unit when the unit shuts down. No more sequenced messages will be delivered for this unit, but heartbeats from the unit may be received. *)
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

  End EndOfSessionMessage.

End CfeFuturesOofMulticastDepthOfBookV108.
