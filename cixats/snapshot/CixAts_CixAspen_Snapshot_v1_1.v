From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * CIX Trading Inc. CIX Tcp Snapshot

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
  *)

Module CixAtsCixAspenSnapshotV11.

  Module PacketHeader.

    (** TcpOut packet header *)
    Record t := {
      length_ : N;
      packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_bytes 1 (packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (packet_type_value, bytes) =>
              Some ({| length_ := length__value; packet_type := packet_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End PacketHeader.

  Module LoginMessage.

    (** The client must login to the server before it will receive data *)
    Record t := {
      user : list byte;
      pass : list byte;
      market_day_identifier : list byte;
      feed_identifier : list byte;
      requested_sequence : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user record) = 6 /\
      Datatypes.length (pass record) = 10 /\
      Datatypes.length (market_day_identifier record) = 9 /\
      Datatypes.length (feed_identifier record) = 1 /\
      Datatypes.length (requested_sequence record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user record) ++
      encode_bytes 10 (pass record) ++
      encode_bytes 9 (market_day_identifier record) ++
      encode_bytes 1 (feed_identifier record) ++
      encode_bytes 20 (requested_sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (pass_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (market_day_identifier_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (feed_identifier_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (requested_sequence_value, bytes) =>
                          Some ({| user := user_value; pass := pass_value; market_day_identifier := market_day_identifier_value; feed_identifier := feed_identifier_value; requested_sequence := requested_sequence_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginMessage.

  Module SuccessfulLoginMessage.

    (** Sent by the server to accept a Login Message *)
    Record t := {
      market_day_identifier : list byte;
      feed_identifier : list byte;
      next_sequence : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_day_identifier record) = 9 /\
      Datatypes.length (feed_identifier record) = 1 /\
      Datatypes.length (next_sequence record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (market_day_identifier record) ++
      encode_bytes 1 (feed_identifier record) ++
      encode_bytes 20 (next_sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (market_day_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (feed_identifier_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (next_sequence_value, bytes) =>
                  Some ({| market_day_identifier := market_day_identifier_value; feed_identifier := feed_identifier_value; next_sequence := next_sequence_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End SuccessfulLoginMessage.

  Module LoginRejectMessage.

    (** Sent by the server to reject a Login Message *)
    Record t := {
      reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reason_code_value, bytes) =>
          Some ({| reason_code := reason_code_value |}, bytes)
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

  End LoginRejectMessage.

  Module MarketEventMessage.

    (** Transitions in the overall session state *)
    Record t := {
      reserved_2 : list byte;
      timestamp : N;
      event : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; timestamp := timestamp_value; event := event_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketEventMessage.

  Module SymbolInformationMessage.

    (** Reference data for each symbol that may be traded *)
    Record t := {
      timestamp : N;
      symbol_id : N;
      symbol : list byte;
      listing_market : list byte;
      board_lot_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (listing_market record) = 1 /\
      (board_lot_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (symbol_id record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (listing_market record) ++
      encode_uint 4 (board_lot_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (listing_market_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (board_lot_size_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol_id := symbol_id_value; symbol := symbol_value; listing_market := listing_market_value; board_lot_size := board_lot_size_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolInformationMessage.

  Module SymbolStateMessage.

    (** Individual symbol trading state (halts) *)
    Record t := {
      timestamp : N;
      symbol_id : N;
      symbol : list byte;
      state : list byte;
      reserved_1 : list byte;
      info : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (state record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (info record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (symbol_id record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (state record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 4 (info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (state_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (info_value, bytes) =>
                              Some ({| timestamp := timestamp_value; symbol_id := symbol_id_value; symbol := symbol_value; state := state_value; reserved_1 := reserved_1_value; info := info_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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

  End SymbolStateMessage.

  Module NewOrderAddMessage.

    (** A new resting order added to the book *)
    Record t := {
      timestamp : N;
      symbol_id : N;
      order_id : N;
      side : list byte;
      quantity : N;
      symbol : list byte;
      price : N;
      broker : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (quantity record) ++
      encode_bytes 11 (symbol record) ++
      encode_uint 8 (price record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (broker_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (reserved_1_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; symbol_id := symbol_id_value; order_id := order_id_value; side := side_value; quantity := quantity_value; symbol := symbol_value; price := price_value; broker := broker_value; reserved_1 := reserved_1_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderAddMessage.

  Module OrderPartialCancelMessage.

    (** Part of a resting order is canceled *)
    Record t := {
      timestamp : N;
      order_id : N;
      quantity_canceled : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_canceled record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity_canceled record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_canceled_value, bytes) =>
                  Some ({| timestamp := timestamp_value; order_id := order_id_value; quantity_canceled := quantity_canceled_value |}, bytes)
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

  End OrderPartialCancelMessage.

  Module OrderCancelAllMessage.

    (** Sent when the order is canceled in its entirety *)
    Record t := {
      timestamp : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              Some ({| timestamp := timestamp_value; order_id := order_id_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderCancelAllMessage.

  Module OrderExecutedMessage.

    (** Sent when an order is executed *)
    Record t := {
      timestamp : N;
      order_id : N;
      quantity : N;
      execution_id : N;
      side : list byte;
      price : N;
      broker : list byte;
      contra_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (execution_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (broker_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (contra_broker_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; order_id := order_id_value; quantity := quantity_value; execution_id := execution_id_value; side := side_value; price := price_value; broker := broker_value; contra_broker := contra_broker_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module EndOfSnapshotMessage.

    (** Sent once the snapshot has completed *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End EndOfSnapshotMessage.

End CixAtsCixAspenSnapshotV11.
