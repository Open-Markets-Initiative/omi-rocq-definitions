From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Net Order Imbalance View

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

Module NsmEquitiesNoiViewV212012.

  Module PacketHeader.

    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      timestamp : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (timestamp record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| timestamp := timestamp_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End MessageHeader.

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
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

  Module StockDirectoryMessage.

    (** At the start of each trading day, NASDAQ disseminates stock directory messages for all active symbols in Single Book. *)
    Record t := {
      stock : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
      round_lot_size : list byte;
      round_lots_only : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (round_lot_size record) = 6 /\
      Datatypes.length (round_lots_only record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 6 (round_lot_size record) ++
      encode_bytes 1 (round_lots_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_category_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (financial_status_indicator_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (round_lot_size_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (round_lots_only_value, bytes) =>
                          Some ({| stock := stock_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End StockDirectoryMessage.

  Module StockTradingActionMessage.

    (** NASDAQ uses this administrative message to indicate the current trading status of a security to the trading community. *)
    Record t := {
      stock : list byte;
      current_trading_state : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (current_trading_state record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (current_trading_state record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (current_trading_state_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (reason_value, bytes) =>
                  Some ({| stock := stock_value; current_trading_state := current_trading_state_value; reason := reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End StockTradingActionMessage.

  Module RegShoRestrictionMessage.

    (** Denotes the Reg SHO Short Sale Price Test Restriction status for the issue at the time of the message dissemination. *)
    Record t := {
      stock : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reg_sho_action_value, bytes) =>
              Some ({| stock := stock_value; reg_sho_action := reg_sho_action_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End RegShoRestrictionMessage.

  Module NoiiMessage.

    (** NASDAQ disseminates NOII data at 5-second intervals in the minutes leading up to the NASDAQ Opening and Closing Crosses as well as the IPO/Halt Crosses. *)
    Record t := {
      paired_shares : list byte;
      imbalance_shares : list byte;
      imbalance_direction : list byte;
      stock : list byte;
      far_price : list byte;
      near_price : list byte;
      current_reference_price : list byte;
      cross_type : list byte;
      price_variation_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (paired_shares record) = 9 /\
      Datatypes.length (imbalance_shares record) = 9 /\
      Datatypes.length (imbalance_direction record) = 1 /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (far_price record) = 10 /\
      Datatypes.length (near_price record) = 10 /\
      Datatypes.length (current_reference_price record) = 10 /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (price_variation_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (paired_shares record) ++
      encode_bytes 9 (imbalance_shares record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 10 (far_price record) ++
      encode_bytes 10 (near_price record) ++
      encode_bytes 10 (current_reference_price record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (price_variation_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (paired_shares_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (imbalance_shares_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (imbalance_direction_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (far_price_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (near_price_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (current_reference_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (cross_type_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (price_variation_indicator_value, bytes) =>
                                          Some ({| paired_shares := paired_shares_value; imbalance_shares := imbalance_shares_value; imbalance_direction := imbalance_direction_value; stock := stock_value; far_price := far_price_value; near_price := near_price_value; current_reference_price := current_reference_price_value; cross_type := cross_type_value; price_variation_indicator := price_variation_indicator_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NoiiMessage.

  Module CrossTradeMessage.

    (** Cross Trade message indicates that NASDAQ has completed its cross process for a specific security. *)
    Record t := {
      shares : list byte;
      stock : list byte;
      cross_price : list byte;
      match_number : list byte;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (shares record) = 9 /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (cross_price record) = 10 /\
      Datatypes.length (match_number record) = 12 /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 10 (cross_price record) ++
      encode_bytes 12 (match_number record) ++
      encode_bytes 1 (cross_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (shares_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (stock_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (cross_price_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cross_type_value, bytes) =>
                          Some ({| shares := shares_value; stock := stock_value; cross_price := cross_price_value; match_number := match_number_value; cross_type := cross_type_value |}, bytes)
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

  End CrossTradeMessage.

End NsmEquitiesNoiViewV212012.
