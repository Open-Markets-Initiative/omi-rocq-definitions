From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch

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

Module NsmEquitiesTotalViewV30Udp.

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
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          Some ({| message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module SecondsMessage.

    (** This message is sent every second for which at least one TotalView-ITCH 3.0 message is being generated. *)
    Record t := {
      second : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (second record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (second_value, bytes) =>
          Some ({| second := second_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End SecondsMessage.

  Module MillisecondsMessage.

    (** This message is sent every millisecond for which at least one TotalView-ITCH 3.0 message is being generated. *)
    Record t := {
      millisecond : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (millisecond record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (millisecond record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (millisecond_value, bytes) =>
          Some ({| millisecond := millisecond_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MillisecondsMessage.

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
      stock_alphabetic_6 : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
      round_lot_size : list byte;
      round_lots_only : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_alphabetic_6 record) = 6 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (round_lot_size record) = 6 /\
      Datatypes.length (round_lots_only record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (stock_alphabetic_6 record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 6 (round_lot_size record) ++
      encode_bytes 1 (round_lots_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (stock_alphabetic_6_value, bytes) =>
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
                          Some ({| stock_alphabetic_6 := stock_alphabetic_6_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value |}, bytes)
                      end
                  end
              end
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
      stock_alphanumeric_6 : list byte;
      trading_state : list byte;
      reserved_1 : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_alphanumeric_6 record) = 6 /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (stock_alphanumeric_6 record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (stock_alphanumeric_6_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_state_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      Some ({| stock_alphanumeric_6 := stock_alphanumeric_6_value; trading_state := trading_state_value; reserved_1 := reserved_1_value; reason := reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End StockTradingActionMessage.

  Module MarketParticipantPositionMessage.

    (** At the start of each trading day, NASDAQ disseminates a spin of market participant position messages. Throughout the day, NASDAQ will send out this message only if NASDAQ Operations changes the status of a market participant firm in an issue. *)
    Record t := {
      mpid : list byte;
      stock_alphanumeric_6 : list byte;
      primary_market_maker : list byte;
      market_maker_mode : list byte;
      market_participant_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (stock_alphanumeric_6 record) = 6 /\
      Datatypes.length (primary_market_maker record) = 1 /\
      Datatypes.length (market_maker_mode record) = 1 /\
      Datatypes.length (market_participant_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (mpid record) ++
      encode_bytes 6 (stock_alphanumeric_6 record) ++
      encode_bytes 1 (primary_market_maker record) ++
      encode_bytes 1 (market_maker_mode record) ++
      encode_bytes 1 (market_participant_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (mpid_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (stock_alphanumeric_6_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (primary_market_maker_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_maker_mode_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (market_participant_state_value, bytes) =>
                          Some ({| mpid := mpid_value; stock_alphanumeric_6 := stock_alphanumeric_6_value; primary_market_maker := primary_market_maker_value; market_maker_mode := market_maker_mode_value; market_participant_state := market_participant_state_value |}, bytes)
                      end
                  end
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

  End MarketParticipantPositionMessage.

  Module AddOrderMessage.

    (** An Add Order Message indicates that a new order has been accepted by the NASDAQ system and was added to the displayable book. This message will be generated for unattributed orders in the NASDAQ Single Book system. *)
    Record t := {
      order_reference_number : list byte;
      side : list byte;
      shares_numeric_6 : list byte;
      stock_alphanumeric_6 : list byte;
      price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (shares_numeric_6 record) = 6 /\
      Datatypes.length (stock_alphanumeric_6 record) = 6 /\
      Datatypes.length (price record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (shares_numeric_6 record) ++
      encode_bytes 6 (stock_alphanumeric_6 record) ++
      encode_bytes 10 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_numeric_6_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (stock_alphanumeric_6_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| order_reference_number := order_reference_number_value; side := side_value; shares_numeric_6 := shares_numeric_6_value; stock_alphanumeric_6 := stock_alphanumeric_6_value; price := price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End AddOrderMessage.

  Module AddOrderWithMpidMessage.

    (** This message will be generated for attributed orders and quotations entered into the NASDAQ Single Book system. *)
    Record t := {
      order_reference_number : list byte;
      side : list byte;
      shares_numeric_6 : list byte;
      stock_alphanumeric_6 : list byte;
      price : list byte;
      attribution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (shares_numeric_6 record) = 6 /\
      Datatypes.length (stock_alphanumeric_6 record) = 6 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (attribution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (shares_numeric_6 record) ++
      encode_bytes 6 (stock_alphanumeric_6 record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 4 (attribution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_numeric_6_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (stock_alphanumeric_6_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (attribution_value, bytes) =>
                              Some ({| order_reference_number := order_reference_number_value; side := side_value; shares_numeric_6 := shares_numeric_6_value; stock_alphanumeric_6 := stock_alphanumeric_6_value; price := price_value; attribution := attribution_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End AddOrderWithMpidMessage.

  Module OrderExecutedMessage.

    (** This message is sent whenever an order on the book is executed in whole or in part. *)
    Record t := {
      order_reference_number : list byte;
      executed_shares : list byte;
      match_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (executed_shares record) = 6 /\
      Datatypes.length (match_number record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 6 (executed_shares record) ++
      encode_bytes 9 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_number_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (executed_shares_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (match_number_value, bytes) =>
                  Some ({| order_reference_number := order_reference_number_value; executed_shares := executed_shares_value; match_number := match_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** This message is sent whenever an order on the book is executed in whole or in part at a price different from the initial display price. *)
    Record t := {
      order_reference_number : list byte;
      executed_shares : list byte;
      match_number : list byte;
      printable : list byte;
      execution_price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (executed_shares record) = 6 /\
      Datatypes.length (match_number record) = 9 /\
      Datatypes.length (printable record) = 1 /\
      Datatypes.length (execution_price record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 6 (executed_shares record) ++
      encode_bytes 9 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_bytes 10 (execution_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_number_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (executed_shares_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (match_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (printable_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          Some ({| order_reference_number := order_reference_number_value; executed_shares := executed_shares_value; match_number := match_number_value; printable := printable_value; execution_price := execution_price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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

  End OrderExecutedWithPriceMessage.

  Module OrderCancelMessage.

    (** This message is sent whenever an order on the book is modified as a result of a partial cancellation. *)
    Record t := {
      order_reference_number : list byte;
      canceled_shares : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (canceled_shares record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 6 (canceled_shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_number_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (canceled_shares_value, bytes) =>
              Some ({| order_reference_number := order_reference_number_value; canceled_shares := canceled_shares_value |}, bytes)
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

  Module OrderDeleteMessage.

    (** This message is sent whenever an order on the book is being cancelled. All remaining shares are no longer accessible so the order should be removed from the book. *)
    Record t := {
      order_reference_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference_number record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_number_value, bytes) =>
          Some ({| order_reference_number := order_reference_number_value |}, bytes)
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

  End OrderDeleteMessage.

  Module TradeMessage.

    (** The Trade Message is designed to provide execution details for normal match events involving non-displayable order types. *)
    Record t := {
      order_reference_number : list byte;
      side : list byte;
      shares_numeric_6 : list byte;
      stock_alphanumeric_6 : list byte;
      price : list byte;
      match_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference_number record) = 9 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (shares_numeric_6 record) = 6 /\
      Datatypes.length (stock_alphanumeric_6 record) = 6 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (match_number record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference_number record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 6 (shares_numeric_6 record) ++
      encode_bytes 6 (stock_alphanumeric_6 record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 9 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_numeric_6_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (stock_alphanumeric_6_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              Some ({| order_reference_number := order_reference_number_value; side := side_value; shares_numeric_6 := shares_numeric_6_value; stock_alphanumeric_6 := stock_alphanumeric_6_value; price := price_value; match_number := match_number_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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

  End TradeMessage.

  Module CrossTradeMessage.

    (** Cross Trade message indicates that NASDAQ has completed its cross process for a specific security. *)
    Record t := {
      shares_numeric_9 : list byte;
      stock_alphanumeric_6 : list byte;
      cross_price : list byte;
      match_number : list byte;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (shares_numeric_9 record) = 9 /\
      Datatypes.length (stock_alphanumeric_6 record) = 6 /\
      Datatypes.length (cross_price record) = 10 /\
      Datatypes.length (match_number record) = 9 /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (shares_numeric_9 record) ++
      encode_bytes 6 (stock_alphanumeric_6 record) ++
      encode_bytes 10 (cross_price record) ++
      encode_bytes 9 (match_number record) ++
      encode_bytes 1 (cross_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (shares_numeric_9_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (stock_alphanumeric_6_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (cross_price_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (cross_type_value, bytes) =>
                          Some ({| shares_numeric_9 := shares_numeric_9_value; stock_alphanumeric_6 := stock_alphanumeric_6_value; cross_price := cross_price_value; match_number := match_number_value; cross_type := cross_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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

  Module BrokenTradeMessage.

    (** The Broken Trade Message is sent whenever an execution on NASDAQ is broken. *)
    Record t := {
      match_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (match_number record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (match_number_value, bytes) =>
          Some ({| match_number := match_number_value |}, bytes)
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

  Module NetOrderImbalanceIndicatorMessage.

    (** NOII data is disseminated at 5-second intervals in the minutes leading up to the NASDAQ Opening Cross, NASDAQ Closing Cross, and NASDAQ IPO/Halt Cross. *)
    Record t := {
      paired_shares : list byte;
      imbalance_shares : list byte;
      imbalance_direction : list byte;
      stock_alphanumeric_6 : list byte;
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
      Datatypes.length (stock_alphanumeric_6 record) = 6 /\
      Datatypes.length (far_price record) = 10 /\
      Datatypes.length (near_price record) = 10 /\
      Datatypes.length (current_reference_price record) = 10 /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (price_variation_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (paired_shares record) ++
      encode_bytes 9 (imbalance_shares record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_bytes 6 (stock_alphanumeric_6 record) ++
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
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (stock_alphanumeric_6_value, bytes) =>
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
                                          Some ({| paired_shares := paired_shares_value; imbalance_shares := imbalance_shares_value; imbalance_direction := imbalance_direction_value; stock_alphanumeric_6 := stock_alphanumeric_6_value; far_price := far_price_value; near_price := near_price_value; current_reference_price := current_reference_price_value; cross_type := cross_type_value; price_variation_indicator := price_variation_indicator_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
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

  End NetOrderImbalanceIndicatorMessage.

End NsmEquitiesTotalViewV30Udp.
