From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Multicast Trades

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
  *)

Module NeoEquitiesMulticastTradesV1014.

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

  Module UnitClearMessage.

    (** Instructs feed recipients to clear all orders for the Cboe Canada order book in the unit specified in the Sequenced Unit Header. Distributed in rare recovery events such as a data center fail-over. *)
    Record t := {
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reserved_4_value, bytes) =>
          Some ({| reserved_4 := reserved_4_value |}, bytes)
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

  Module TradingStatusMessage.

    (** Indicates the current trading status of a security on the Cboe Canada NEO system. Sequenced Trading Status messages are sent upon system startup for all active securities with Trading Status = S (suspended). *)
    Record t := {
      timestamp : N;
      order_book_type : N;
      symbol : list byte;
      trading_status : list byte;
      trading_sub_status : list byte;
      halt_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_book_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (symbol record) = 14 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (trading_sub_status record) = 1 /\
      Datatypes.length (halt_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 1 (order_book_type record) ++
      encode_bytes 14 (symbol record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 1 (trading_sub_status record) ++
      encode_bytes 1 (halt_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (order_book_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (trading_sub_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (halt_reason_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_book_type := order_book_type_value; symbol := symbol_value; trading_status := trading_status_value; trading_sub_status := trading_sub_status_value; halt_reason := halt_reason_value |}, bytes)
                          end
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module TradeBreakMessage.

    (** Sent whenever an execution on Cboe Canada NEO is cancelled. Applications that simply build a Cboe Canada NEO book can ignore Trade Break messages. *)
    Record t := {
      timestamp : N;
      order_book_type : N;
      symbol : list byte;
      original_quantity : N;
      original_price : N;
      execution_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_book_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (symbol record) = 14 /\
      (original_quantity record < 256 ^ N.of_nat 4)%N /\
      (original_price record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 1 (order_book_type record) ++
      encode_bytes 14 (symbol record) ++
      encode_uint 4 (original_quantity record) ++
      encode_uint 8 (original_price record) ++
      encode_uint 8 (execution_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (order_book_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (execution_id_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_book_type := order_book_type_value; symbol := symbol_value; original_quantity := original_quantity_value; original_price := original_price_value; execution_id := execution_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeBreakMessage.

  Module TradeCorrectionMessage.

    (** Sent whenever an execution on Cboe Canada NEO is corrected. Applications that simply build a Cboe Canada NEO book can ignore Trade Correction messages. *)
    Record t := {
      timestamp : N;
      order_book_type : N;
      symbol : list byte;
      original_quantity : N;
      original_price : N;
      original_settlement_type : N;
      original_settlement_date : N;
      corrected_quantity : N;
      corrected_price : N;
      corrected_settlement_type : N;
      corrected_settlement_date : N;
      execution_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_book_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (symbol record) = 14 /\
      (original_quantity record < 256 ^ N.of_nat 4)%N /\
      (original_price record < 256 ^ N.of_nat 8)%N /\
      (original_settlement_type record < 256 ^ N.of_nat 1)%N /\
      (original_settlement_date record < 256 ^ N.of_nat 4)%N /\
      (corrected_quantity record < 256 ^ N.of_nat 4)%N /\
      (corrected_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_settlement_type record < 256 ^ N.of_nat 1)%N /\
      (corrected_settlement_date record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 1 (order_book_type record) ++
      encode_bytes 14 (symbol record) ++
      encode_uint 4 (original_quantity record) ++
      encode_uint 8 (original_price record) ++
      encode_uint 1 (original_settlement_type record) ++
      encode_uint 4 (original_settlement_date record) ++
      encode_uint 4 (corrected_quantity record) ++
      encode_uint 8 (corrected_price record) ++
      encode_uint 1 (corrected_settlement_type record) ++
      encode_uint 4 (corrected_settlement_date record) ++
      encode_uint 8 (execution_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (order_book_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_price_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (original_settlement_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (original_settlement_date_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (corrected_quantity_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (corrected_price_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (corrected_settlement_type_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (corrected_settlement_date_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (execution_id_value, bytes) =>
                                                      Some ({| timestamp := timestamp_value; order_book_type := order_book_type_value; symbol := symbol_value; original_quantity := original_quantity_value; original_price := original_price_value; original_settlement_type := original_settlement_type_value; original_settlement_date := original_settlement_date_value; corrected_quantity := corrected_quantity_value; corrected_price := corrected_price_value; corrected_settlement_type := corrected_settlement_type_value; corrected_settlement_date := corrected_settlement_date_value; execution_id := execution_id_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module EndOfSessionMessage.

    (** Sent for each unit when the unit shuts down. No additional sequenced messages will be delivered for this unit, but heartbeats from the unit may be received. *)
    Record t := {
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reserved_4_value, bytes) =>
          Some ({| reserved_4 := reserved_4_value |}, bytes)
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

End NeoEquitiesMulticastTradesV1014.
