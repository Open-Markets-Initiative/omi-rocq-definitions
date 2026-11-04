From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * 24 National Exchange Member Order Information Record Depth Feed

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
      - a length prefix framing what follows
      - a field read in bits
      - a block whose stated length holds more than its fields

    License: MIT No Attribution
  *)

Module v24XEquitiesMemoirDepthFeedV20.

  Module CommonHeader.

    (** Memx Udp Common Header *)
    Record t := {
      message_type : N;
      header_length : N;
      session_id : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_type record < 256 ^ N.of_nat 1)%N /\
      (header_length record < 256 ^ N.of_nat 1)%N /\
      (session_id record < 256 ^ N.of_nat 8)%N /\
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_type record) ++
      encode_uint 1 (header_length record) ++
      encode_uint 8 (session_id record) ++
      encode_uint 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (header_length_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      Some ({| message_type := message_type_value; header_length := header_length_value; session_id := session_id_value; sequence_number := sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End CommonHeader.

  Module SbeHeader.

    (** Sbe Header *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 1)%N /\
      (schema_id record < 256 ^ N.of_nat 1)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (template_id record) ++
      encode_uint 1 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
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

  End SbeHeader.

  Module InstrumentDirectoryMessage.

    (** InstrumentDirectoryMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      symbol : list byte;
      symbol_sfx : list byte;
      round_lot : N;
      is_test_symbol : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (symbol_sfx record) = 6 /\
      (round_lot record < 256 ^ N.of_nat 4)%N /\
      (is_test_symbol record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 6 (symbol_sfx record) ++
      encode_uint 4 (round_lot record) ++
      encode_uint 1 (is_test_symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (symbol_sfx_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (round_lot_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (is_test_symbol_value, bytes) =>
                              Some ({| timestamp := timestamp_value; security_id := security_id_value; symbol := symbol_value; symbol_sfx := symbol_sfx_value; round_lot := round_lot_value; is_test_symbol := is_test_symbol_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentDirectoryMessage.

  Module RegShoRestrictionMessage.

    (** RegSHORestrictionMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      short_sale_restriction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (short_sale_restriction record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 1 (short_sale_restriction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (short_sale_restriction_value, bytes) =>
                  Some ({| timestamp := timestamp_value; security_id := security_id_value; short_sale_restriction := short_sale_restriction_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End RegShoRestrictionMessage.

  Module SecurityTradingStatusMessage.

    (** SecurityTradingStatusMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      security_trading_status : list byte;
      security_trading_status_reason : list byte;
      halt_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (security_trading_status record) = 1 /\
      Datatypes.length (security_trading_status_reason record) = 1 /\
      (halt_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_bytes 1 (security_trading_status record) ++
      encode_bytes 1 (security_trading_status_reason record) ++
      encode_uint 1 (halt_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_trading_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (security_trading_status_reason_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (halt_reason_value, bytes) =>
                          Some ({| timestamp := timestamp_value; security_id := security_id_value; security_trading_status := security_trading_status_value; security_trading_status_reason := security_trading_status_reason_value; halt_reason := halt_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End SecurityTradingStatusMessage.

  Module TradingSessionStatusMessage.

    (** TradingSessionStatusMessage *)
    Record t := {
      timestamp : N;
      trading_session : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_session record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (trading_session record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_session_value, bytes) =>
              Some ({| timestamp := timestamp_value; trading_session := trading_session_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingSessionStatusMessage.

  Module OrderDeletedMessage.

    (** OrderDeletedMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  Some ({| timestamp := timestamp_value; security_id := security_id_value; order_id := order_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End OrderDeletedMessage.

  Module OrderReducedMessage.

    (** OrderReducedMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      order_id : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      Some ({| timestamp := timestamp_value; security_id := security_id_value; order_id := order_id_value; quantity := quantity_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End OrderReducedMessage.

  Module OrderExecutedMessage.

    (** OrderExecutedMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      order_id : N;
      trade_id : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; security_id := security_id_value; order_id := order_id_value; trade_id := trade_id_value; quantity := quantity_value; price := price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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

  End OrderExecutedMessage.

  Module TradeMessage.

    (** TradeMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      trade_id : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| timestamp := timestamp_value; security_id := security_id_value; trade_id := trade_id_value; quantity := quantity_value; price := price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End TradeMessage.

  Module BrokenTradeMessage.

    (** BrokenTradeMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      trade_id : N;
      original_quantity : N;
      original_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (original_quantity record < 256 ^ N.of_nat 4)%N /\
      (original_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (original_quantity record) ++
      encode_uint 8 (original_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_price_value, bytes) =>
                          Some ({| timestamp := timestamp_value; security_id := security_id_value; trade_id := trade_id_value; original_quantity := original_quantity_value; original_price := original_price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End BrokenTradeMessage.

  Module CorrectedTradeMessage.

    (** CorrectedTradeMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      trade_id : N;
      original_quantity : N;
      original_price : N;
      corrected_quantity : N;
      corrected_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (original_quantity record < 256 ^ N.of_nat 4)%N /\
      (original_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_quantity record < 256 ^ N.of_nat 4)%N /\
      (corrected_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (original_quantity record) ++
      encode_uint 8 (original_price record) ++
      encode_uint 4 (corrected_quantity record) ++
      encode_uint 8 (corrected_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (corrected_quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (corrected_price_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; security_id := security_id_value; trade_id := trade_id_value; original_quantity := original_quantity_value; original_price := original_price_value; corrected_quantity := corrected_quantity_value; corrected_price := corrected_price_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End CorrectedTradeMessage.

  Module ClearBookMessage.

    (** ClearBookMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              Some ({| timestamp := timestamp_value; security_id := security_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End ClearBookMessage.

  Module AuctionStatusMessage.

    (** AuctionStatusMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      auction_id : N;
      auction_type : list byte;
      tie_breaker_price : N;
      lower_collar_price : N;
      upper_collar_price : N;
      reference_price : N;
      reference_buy_quantity : N;
      reference_sell_quantity : N;
      indicative_price : N;
      auction_only_price : N;
      number_of_extensions : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (tie_breaker_price record < 256 ^ N.of_nat 8)%N /\
      (lower_collar_price record < 256 ^ N.of_nat 8)%N /\
      (upper_collar_price record < 256 ^ N.of_nat 8)%N /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (reference_buy_quantity record < 256 ^ N.of_nat 8)%N /\
      (reference_sell_quantity record < 256 ^ N.of_nat 8)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (auction_only_price record < 256 ^ N.of_nat 8)%N /\
      (number_of_extensions record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (auction_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (tie_breaker_price record) ++
      encode_uint 8 (lower_collar_price record) ++
      encode_uint 8 (upper_collar_price record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (reference_buy_quantity record) ++
      encode_uint 8 (reference_sell_quantity record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 8 (auction_only_price record) ++
      encode_uint 4 (number_of_extensions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (auction_type_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (tie_breaker_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (lower_collar_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (upper_collar_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (reference_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (reference_buy_quantity_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (reference_sell_quantity_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (indicative_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (auction_only_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (number_of_extensions_value, bytes) =>
                                                          Some ({| timestamp := timestamp_value; security_id := security_id_value; auction_id := auction_id_value; auction_type := auction_type_value; tie_breaker_price := tie_breaker_price_value; lower_collar_price := lower_collar_price_value; upper_collar_price := upper_collar_price_value; reference_price := reference_price_value; reference_buy_quantity := reference_buy_quantity_value; reference_sell_quantity := reference_sell_quantity_value; indicative_price := indicative_price_value; auction_only_price := auction_only_price_value; number_of_extensions := number_of_extensions_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 87.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionStatusMessage.

  Module AuctionTradeMessage.

    (** AuctionTradeMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      auction_id : N;
      auction_type : list byte;
      auction_quantity : N;
      auction_price : N;
      trade_id : N;
      sale_condition_1 : list byte;
      sale_condition_2 : list byte;
      sale_condition_3 : list byte;
      sale_condition_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_quantity record < 256 ^ N.of_nat 8)%N /\
      (auction_price record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sale_condition_1 record) = 1 /\
      Datatypes.length (sale_condition_2 record) = 1 /\
      Datatypes.length (sale_condition_3 record) = 1 /\
      Datatypes.length (sale_condition_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (auction_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (auction_quantity record) ++
      encode_uint 8 (auction_price record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 1 (sale_condition_1 record) ++
      encode_bytes 1 (sale_condition_2 record) ++
      encode_bytes 1 (sale_condition_3 record) ++
      encode_bytes 1 (sale_condition_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (auction_type_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (auction_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (auction_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (sale_condition_2_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sale_condition_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (sale_condition_4_value, bytes) =>
                                                  Some ({| timestamp := timestamp_value; security_id := security_id_value; auction_id := auction_id_value; auction_type := auction_type_value; auction_quantity := auction_quantity_value; auction_price := auction_price_value; trade_id := trade_id_value; sale_condition_1 := sale_condition_1_value; sale_condition_2 := sale_condition_2_value; sale_condition_3 := sale_condition_3_value; sale_condition_4 := sale_condition_4_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionTradeMessage.

  Module BrokenAuctionTradeMessage.

    (** BrokenAuctionTradeMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      auction_id : N;
      trade_id : N;
      original_auction_quantity : N;
      original_auction_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (original_auction_quantity record < 256 ^ N.of_nat 8)%N /\
      (original_auction_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (auction_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (original_auction_quantity record) ++
      encode_uint 8 (original_auction_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_auction_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (original_auction_price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; security_id := security_id_value; auction_id := auction_id_value; trade_id := trade_id_value; original_auction_quantity := original_auction_quantity_value; original_auction_price := original_auction_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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

  End BrokenAuctionTradeMessage.

  Module CorrectedAuctionTradeMessage.

    (** CorrectedAuctionTradeMessage *)
    Record t := {
      timestamp : N;
      security_id : N;
      auction_id : N;
      trade_id : N;
      original_auction_quantity : N;
      original_auction_price : N;
      original_sale_condition_1 : list byte;
      original_sale_condition_2 : list byte;
      original_sale_condition_3 : list byte;
      original_sale_condition_4 : list byte;
      corrected_auction_quantity : N;
      corrected_auction_price : N;
      corrected_sale_condition_1 : list byte;
      corrected_sale_condition_2 : list byte;
      corrected_sale_condition_3 : list byte;
      corrected_sale_condition_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (original_auction_quantity record < 256 ^ N.of_nat 8)%N /\
      (original_auction_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (original_sale_condition_1 record) = 1 /\
      Datatypes.length (original_sale_condition_2 record) = 1 /\
      Datatypes.length (original_sale_condition_3 record) = 1 /\
      Datatypes.length (original_sale_condition_4 record) = 1 /\
      (corrected_auction_quantity record < 256 ^ N.of_nat 8)%N /\
      (corrected_auction_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (corrected_sale_condition_1 record) = 1 /\
      Datatypes.length (corrected_sale_condition_2 record) = 1 /\
      Datatypes.length (corrected_sale_condition_3 record) = 1 /\
      Datatypes.length (corrected_sale_condition_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (auction_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (original_auction_quantity record) ++
      encode_uint 8 (original_auction_price record) ++
      encode_bytes 1 (original_sale_condition_1 record) ++
      encode_bytes 1 (original_sale_condition_2 record) ++
      encode_bytes 1 (original_sale_condition_3 record) ++
      encode_bytes 1 (original_sale_condition_4 record) ++
      encode_uint 8 (corrected_auction_quantity record) ++
      encode_uint 8 (corrected_auction_price record) ++
      encode_bytes 1 (corrected_sale_condition_1 record) ++
      encode_bytes 1 (corrected_sale_condition_2 record) ++
      encode_bytes 1 (corrected_sale_condition_3 record) ++
      encode_bytes 1 (corrected_sale_condition_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_auction_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (original_auction_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (original_sale_condition_1_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (original_sale_condition_2_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (original_sale_condition_3_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (original_sale_condition_4_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (corrected_auction_quantity_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (corrected_auction_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (corrected_sale_condition_1_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (corrected_sale_condition_2_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (corrected_sale_condition_3_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (corrected_sale_condition_4_value, bytes) =>
                                                                      Some ({| timestamp := timestamp_value; security_id := security_id_value; auction_id := auction_id_value; trade_id := trade_id_value; original_auction_quantity := original_auction_quantity_value; original_auction_price := original_auction_price_value; original_sale_condition_1 := original_sale_condition_1_value; original_sale_condition_2 := original_sale_condition_2_value; original_sale_condition_3 := original_sale_condition_3_value; original_sale_condition_4 := original_sale_condition_4_value; corrected_auction_quantity := corrected_auction_quantity_value; corrected_auction_price := corrected_auction_price_value; corrected_sale_condition_1 := corrected_sale_condition_1_value; corrected_sale_condition_2 := corrected_sale_condition_2_value; corrected_sale_condition_3 := corrected_sale_condition_3_value; corrected_sale_condition_4 := corrected_sale_condition_4_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CorrectedAuctionTradeMessage.

  Module SnapshotCompleteMessage.

    (** SnapshotCompleteMessage *)
    Record t := {
      timestamp : N;
      as_of_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (as_of_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (as_of_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (as_of_sequence_number_value, bytes) =>
              Some ({| timestamp := timestamp_value; as_of_sequence_number := as_of_sequence_number_value |}, bytes)
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

  End SnapshotCompleteMessage.

End v24XEquitiesMemoirDepthFeedV20.
