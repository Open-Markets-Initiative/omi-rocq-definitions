From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Long-Term Stock Exchange Member Order Information Record Top Of Book

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

Module LtseEquitiesMemoirTopOfBookV20.

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

End LtseEquitiesMemoirTopOfBookV20.
