From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) CHIXMMD Multicast Market Data

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
      - a run counted by a field
  *)

Module NasdaqCanadaChixmmdV1135.

  Module PacketHeader.

    (** CHIXMMD multicast packet header *)
    Record t := {
      sequence : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              Some ({| sequence := sequence_value; message_count := message_count_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End PacketHeader.

  Module Heartbeat.

    (** The heartbeat carries the current session of the market data stream, to be used in the Login Request of the recovery service *)
    Record t := {
      session : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          Some ({| session := session_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End Heartbeat.

  Module MessageHeader.

    (** Length of the market data message, then its timestamp and type *)
    Record t := {
      length_ : N;
      timestamp : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_bytes 8 (timestamp record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  Some ({| length_ := length__value; timestamp := timestamp_value; message_type := message_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End MessageHeader.

  Module AddOrderMessage.

    (** An Add Order Message indicates that CXC or CX2 has accepted a visible order into the book. It includes a day-unique Order Reference key assigned to the order. The issuing of an Add Order Message is not necessarily always for a new order (see Modification of Existing Orders). Not applicable to CXD. *)
    Record t := {
      order_reference : list byte;
      buy_sell_indicator : list byte;
      shares : list byte;
      stock : list byte;
      price : list byte;
      broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (shares record) = 6 /\
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 6 (shares record) ++
      encode_bytes 10 (stock record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 3 (broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (buy_sell_indicator_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (broker_value, bytes) =>
                              Some ({| order_reference := order_reference_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; broker := broker_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module LongFormAddOrderMessage.

    (** An Add Order Message indicates that CXC or CX2 has accepted a visible order into the book. It includes a day-unique Order Reference key assigned to the order. The issuing of an Add Order Message is not necessarily always for a new order (see Modification of Existing Orders). Not applicable to CXD. Long form messages are used when either the price or size is larger than the standard messages can permit. *)
    Record t := {
      order_reference : list byte;
      buy_sell_indicator : list byte;
      long_shares : list byte;
      stock : list byte;
      long_price : list byte;
      broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (long_shares record) = 10 /\
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (long_price record) = 19 /\
      Datatypes.length (broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 10 (long_shares record) ++
      encode_bytes 10 (stock record) ++
      encode_bytes 19 (long_price record) ++
      encode_bytes 3 (broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (buy_sell_indicator_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (long_shares_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_bytes 19 bytes with
                      | None => None
                      | Some (long_price_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (broker_value, bytes) =>
                              Some ({| order_reference := order_reference_value; buy_sell_indicator := buy_sell_indicator_value; long_shares := long_shares_value; stock := stock_value; long_price := long_price_value; broker := broker_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongFormAddOrderMessage.

  Module OrderExecutionMessage.

    (** An Order Execution Message is sent whenever an order on the book is executed in whole or in part. Not applicable to CXD. *)
    Record t := {
      order_reference : list byte;
      executed_shares : list byte;
      trade_reference : list byte;
      contra_order_reference : list byte;
      trade_attribute : list byte;
      broker : list byte;
      contra_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (executed_shares record) = 6 /\
      Datatypes.length (trade_reference record) = 9 /\
      Datatypes.length (contra_order_reference record) = 9 /\
      Datatypes.length (trade_attribute record) = 1 /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 6 (executed_shares record) ++
      encode_bytes 9 (trade_reference record) ++
      encode_bytes 9 (contra_order_reference record) ++
      encode_bytes 1 (trade_attribute record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (executed_shares_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (trade_reference_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (contra_order_reference_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (trade_attribute_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (broker_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (contra_broker_value, bytes) =>
                                  Some ({| order_reference := order_reference_value; executed_shares := executed_shares_value; trade_reference := trade_reference_value; contra_order_reference := contra_order_reference_value; trade_attribute := trade_attribute_value; broker := broker_value; contra_broker := contra_broker_value |}, bytes)
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

  End OrderExecutionMessage.

  Module LongFormOrderExecutionMessage.

    (** An Order Execution Message is sent whenever an order on the book is executed in whole or in part. Not applicable to CXD. Long form messages are used when either the price or size is larger than the standard messages can permit. *)
    Record t := {
      order_reference : list byte;
      long_executed_shares : list byte;
      trade_reference : list byte;
      contra_order_reference : list byte;
      trade_attribute : list byte;
      broker : list byte;
      contra_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (long_executed_shares record) = 10 /\
      Datatypes.length (trade_reference record) = 9 /\
      Datatypes.length (contra_order_reference record) = 9 /\
      Datatypes.length (trade_attribute record) = 1 /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 10 (long_executed_shares record) ++
      encode_bytes 9 (trade_reference record) ++
      encode_bytes 9 (contra_order_reference record) ++
      encode_bytes 1 (trade_attribute record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (long_executed_shares_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (trade_reference_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (contra_order_reference_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (trade_attribute_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (broker_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (contra_broker_value, bytes) =>
                                  Some ({| order_reference := order_reference_value; long_executed_shares := long_executed_shares_value; trade_reference := trade_reference_value; contra_order_reference := contra_order_reference_value; trade_attribute := trade_attribute_value; broker := broker_value; contra_broker := contra_broker_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End LongFormOrderExecutionMessage.

  Module OrderCancelMessage.

    (** An Order Cancel Message is sent whenever an order on the book is fully canceled, its quantity revised down or when a pegged order is re-priced. Not applicable to CXD. *)
    Record t := {
      order_reference : list byte;
      canceled_shares : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (canceled_shares record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 6 (canceled_shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (canceled_shares_value, bytes) =>
              Some ({| order_reference := order_reference_value; canceled_shares := canceled_shares_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End OrderCancelMessage.

  Module LongFormOrderCancelMessage.

    (** An Order Cancel Message is sent whenever an order on the book is fully canceled, its quantity revised down or when a pegged order is re-priced. Not applicable to CXD. Long form messages are used when either the price or size is larger than the standard messages can permit. *)
    Record t := {
      order_reference : list byte;
      long_canceled_shares : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (long_canceled_shares record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 10 (long_canceled_shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (long_canceled_shares_value, bytes) =>
              Some ({| order_reference := order_reference_value; long_canceled_shares := long_canceled_shares_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End LongFormOrderCancelMessage.

  Module TradeMessage.

    (** A Trade Message is sent when a trade occurs against order quantity not visible on the book (i.e. a fully or partially hidden order). They do not affect the book. The Order Reference is always 0 and the Buy/Sell indicator B. *)
    Record t := {
      order_reference : list byte;
      buy_sell_indicator : list byte;
      shares : list byte;
      stock : list byte;
      price : list byte;
      trade_reference : list byte;
      contra_order_reference : list byte;
      broker : list byte;
      contra_broker : list byte;
      trade_attribute : list byte;
      cross_type : list byte;
      settlement_terms : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (shares record) = 6 /\
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (trade_reference record) = 9 /\
      Datatypes.length (contra_order_reference record) = 9 /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3 /\
      Datatypes.length (trade_attribute record) = 1 /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (settlement_terms record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 6 (shares record) ++
      encode_bytes 10 (stock record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 9 (trade_reference record) ++
      encode_bytes 9 (contra_order_reference record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record) ++
      encode_bytes 1 (trade_attribute record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (settlement_terms record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (buy_sell_indicator_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (trade_reference_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (contra_order_reference_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (broker_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (contra_broker_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_attribute_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cross_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (settlement_terms_value, bytes) =>
                                                      Some ({| order_reference := order_reference_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; trade_reference := trade_reference_value; contra_order_reference := contra_order_reference_value; broker := broker_value; contra_broker := contra_broker_value; trade_attribute := trade_attribute_value; cross_type := cross_type_value; settlement_terms := settlement_terms_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module LongFormTradeMessage.

    (** A Trade Message is sent when a trade occurs against order quantity not visible on the book (i.e. a fully or partially hidden order). They do not affect the book. The Order Reference is always 0 and the Buy/Sell indicator B. Long form messages are used when either the price or size is larger than the standard messages can permit. *)
    Record t := {
      order_reference : list byte;
      buy_sell_indicator : list byte;
      long_shares : list byte;
      stock : list byte;
      long_price : list byte;
      trade_reference : list byte;
      contra_order_reference : list byte;
      broker : list byte;
      contra_broker : list byte;
      trade_attribute : list byte;
      cross_type : list byte;
      settlement_terms : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (long_shares record) = 10 /\
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (long_price record) = 19 /\
      Datatypes.length (trade_reference record) = 9 /\
      Datatypes.length (contra_order_reference record) = 9 /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3 /\
      Datatypes.length (trade_attribute record) = 1 /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (settlement_terms record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 10 (long_shares record) ++
      encode_bytes 10 (stock record) ++
      encode_bytes 19 (long_price record) ++
      encode_bytes 9 (trade_reference record) ++
      encode_bytes 9 (contra_order_reference record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record) ++
      encode_bytes 1 (trade_attribute record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (settlement_terms record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (buy_sell_indicator_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (long_shares_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_bytes 19 bytes with
                      | None => None
                      | Some (long_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (trade_reference_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (contra_order_reference_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (broker_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (contra_broker_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_attribute_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cross_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (settlement_terms_value, bytes) =>
                                                      Some ({| order_reference := order_reference_value; buy_sell_indicator := buy_sell_indicator_value; long_shares := long_shares_value; stock := stock_value; long_price := long_price_value; trade_reference := trade_reference_value; contra_order_reference := contra_order_reference_value; broker := broker_value; contra_broker := contra_broker_value; trade_attribute := trade_attribute_value; cross_type := cross_type_value; settlement_terms := settlement_terms_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongFormTradeMessage.

  Module BrokenTradeMessage.

    (** A Broken Trade message is sent whenever an execution is broken. A Broken Trade is final; once a trade is broken it cannot be reinstated. *)
    Record t := {
      trade_reference : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_reference record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (trade_reference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (trade_reference_value, bytes) =>
          Some ({| trade_reference := trade_reference_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End BrokenTradeMessage.

  Module SystemEventMessage.

    (** The system event message type is used to indicate a market state event. *)
    Record t := {
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (event_code_value, bytes) =>
          Some ({| event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module StockStatusMessage.

    (** This message indicates the current trading status of a stock. At the start of day, the feed will send out a stock status message for each of the symbols trading on CXC, CX2 and CXD. Subsequently, stock status messages will be sent when a stock is halted or is released for trading. *)
    Record t := {
      stock : list byte;
      trading_state : list byte;
      reserved_1 : list byte;
      listing_market : list byte;
      board_lot_size : list byte;
      currency : list byte;
      gef_eligible : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (board_lot_size record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (gef_eligible record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (stock record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 4 (board_lot_size record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (gef_eligible record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_state_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (listing_market_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (board_lot_size_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (currency_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (gef_eligible_value, bytes) =>
                                  Some ({| stock := stock_value; trading_state := trading_state_value; reserved_1 := reserved_1_value; listing_market := listing_market_value; board_lot_size := board_lot_size_value; currency := currency_value; gef_eligible := gef_eligible_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End StockStatusMessage.

End NasdaqCanadaChixmmdV1135.
