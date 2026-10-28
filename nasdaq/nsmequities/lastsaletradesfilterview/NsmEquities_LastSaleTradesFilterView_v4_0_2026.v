From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Last Sale Trades FilterView

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

Module NsmEquitiesLastSaleTradesFilterViewV402026.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

    (** Mold Udp 64 Message Header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module SystemEventMessage.

    (** System Event Messages is used to signal key market or data feed control events. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module TradeReportMessage.

    (** The following message is used to relay trade transactions that are reported for the current business day. Please note that Nasdaq only reports one-side of a trade execution on the Last Sale feeds. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      client_timestamp : N;
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      trade_control_number : list byte;
      trade_price : N;
      trade_size : N;
      sale_condition_modifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (client_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (trade_control_number record) = 10 /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_size record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sale_condition_modifier record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (client_timestamp record) ++
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (trade_control_number record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (trade_size record) ++
      encode_bytes 4 (sale_condition_modifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (client_timestamp_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (originating_market_center_identifier_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (issue_symbol_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (security_class_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (trade_control_number_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_size_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (sale_condition_modifier_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; client_timestamp := client_timestamp_value; originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; trade_control_number := trade_control_number_value; trade_price := trade_price_value; trade_size := trade_size_value; sale_condition_modifier := sale_condition_modifier_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeReportMessage.

  Module TradeCancelErrorMessage.

    (** The following message is used in the event that a transaction is cancelled on the same business day that it is reported. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      client_timestamp : N;
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price : N;
      original_trade_size : N;
      original_sale_condition_modifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (client_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_trade_size record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (original_sale_condition_modifier record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (client_timestamp record) ++
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 8 (original_trade_size record) ++
      encode_bytes 4 (original_sale_condition_modifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (client_timestamp_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (originating_market_center_identifier_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (issue_symbol_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (security_class_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (original_trade_control_number_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (original_trade_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (original_trade_size_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (original_sale_condition_modifier_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; client_timestamp := client_timestamp_value; originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelErrorMessage.

  Module TradeCorrectionMessage.

    (** The following message is used in the event that a trade transaction is corrected on the same business day that it is reported. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      client_timestamp : N;
      originating_market_center_identifier : list byte;
      issue_symbol : list byte;
      security_class : list byte;
      original_trade_control_number : list byte;
      original_trade_price : N;
      original_trade_size : N;
      original_sale_condition_modifier : list byte;
      corrected_trade_control_number : list byte;
      corrected_trade_price : N;
      corrected_trade_size : N;
      corrected_sale_condition_modifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (client_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (original_trade_control_number record) = 10 /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_trade_size record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (original_sale_condition_modifier record) = 4 /\
      Datatypes.length (corrected_trade_control_number record) = 10 /\
      (corrected_trade_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_size record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (corrected_sale_condition_modifier record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (client_timestamp record) ++
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (original_trade_control_number record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 8 (original_trade_size record) ++
      encode_bytes 4 (original_sale_condition_modifier record) ++
      encode_bytes 10 (corrected_trade_control_number record) ++
      encode_uint 8 (corrected_trade_price record) ++
      encode_uint 8 (corrected_trade_size record) ++
      encode_bytes 4 (corrected_sale_condition_modifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (client_timestamp_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (originating_market_center_identifier_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (issue_symbol_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (security_class_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (original_trade_control_number_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (original_trade_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (original_trade_size_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (original_sale_condition_modifier_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (corrected_trade_control_number_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (corrected_trade_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (corrected_trade_size_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (corrected_sale_condition_modifier_value, bytes) =>
                                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; client_timestamp := client_timestamp_value; originating_market_center_identifier := originating_market_center_identifier_value; issue_symbol := issue_symbol_value; security_class := security_class_value; original_trade_control_number := original_trade_control_number_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; original_sale_condition_modifier := original_sale_condition_modifier_value; corrected_trade_control_number := corrected_trade_control_number_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_size := corrected_trade_size_value; corrected_sale_condition_modifier := corrected_sale_condition_modifier_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module StockTradingActionMessage.

    (** Nasdaq uses this administrative message to indicate the current trading status of a security to the trading community. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      issue_symbol : list byte;
      security_class : list byte;
      current_trading_state : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (current_trading_state record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 1 (current_trading_state record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (issue_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (security_class_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (current_trading_state_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (reason_value, bytes) =>
                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; issue_symbol := issue_symbol_value; security_class := security_class_value; current_trading_state := current_trading_state_value; reason := reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End StockTradingActionMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Nasdaq processes orders based on the most Reg SHO Restriction status value. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      issue_symbol : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (issue_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reg_sho_action_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; issue_symbol := issue_symbol_value; reg_sho_action := reg_sho_action_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module StockDirectoryMessage.

    (** At the start of each trading day, Nasdaq disseminates stock directory messages for all active Nasdaq and non Nasdaq listed security symbols. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
      round_lot_size : N;
      round_lots_only : list byte;
      issue_classification : list byte;
      issue_sub_type : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      ipo_flag : list byte;
      luld_reference_price_tier : list byte;
      etp_flag : list byte;
      etp_leverage_factor : N;
      inverse_indicator : list byte;
      bloomberg_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (round_lots_only record) = 1 /\
      Datatypes.length (issue_classification record) = 1 /\
      Datatypes.length (issue_sub_type record) = 2 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      Datatypes.length (ipo_flag record) = 1 /\
      Datatypes.length (luld_reference_price_tier record) = 1 /\
      Datatypes.length (etp_flag record) = 1 /\
      (etp_leverage_factor record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (inverse_indicator record) = 1 /\
      Datatypes.length (bloomberg_id record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_bytes 1 (round_lots_only record) ++
      encode_bytes 1 (issue_classification record) ++
      encode_bytes 2 (issue_sub_type record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_bytes 1 (ipo_flag record) ++
      encode_bytes 1 (luld_reference_price_tier record) ++
      encode_bytes 1 (etp_flag record) ++
      encode_uint 4 (etp_leverage_factor record) ++
      encode_bytes 1 (inverse_indicator record) ++
      encode_bytes 12 (bloomberg_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_category_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (financial_status_indicator_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (round_lot_size_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (round_lots_only_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (issue_classification_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (issue_sub_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (authenticity_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (short_sale_threshold_indicator_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (ipo_flag_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (luld_reference_price_tier_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (etp_flag_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (etp_leverage_factor_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (inverse_indicator_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (bloomberg_id_value, bytes) =>
                                                                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value; issue_classification := issue_classification_value; issue_sub_type := issue_sub_type_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; ipo_flag := ipo_flag_value; luld_reference_price_tier := luld_reference_price_tier_value; etp_flag := etp_flag_value; etp_leverage_factor := etp_leverage_factor_value; inverse_indicator := inverse_indicator_value; bloomberg_id := bloomberg_id_value |}, bytes)
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
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockDirectoryMessage.

  Module AdjustedClosingPriceMessage.

    (** At the start of each trading day, Nasdaq disseminates the adjusted closing price for all active symbols in the Nasdaq system. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      issue_symbol : list byte;
      security_class : list byte;
      adjusted_closing_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (issue_symbol record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_uint 8 (adjusted_closing_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (issue_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (security_class_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (adjusted_closing_price_value, bytes) =>
                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; issue_symbol := issue_symbol_value; security_class := security_class_value; adjusted_closing_price := adjusted_closing_price_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AdjustedClosingPriceMessage.

  Module MwcbDeclineLevelMessage.

    (** Informs data recipients what the daily MWCB breach points are set to for the current trading day. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      level_1 : N;
      level_2 : N;
      level_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (level_1 record < 256 ^ N.of_nat 8)%N /\
      (level_2 record < 256 ^ N.of_nat 8)%N /\
      (level_3 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (level_1 record) ++
      encode_uint 8 (level_2 record) ++
      encode_uint 8 (level_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (level_1_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (level_2_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (level_3_value, bytes) =>
                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; level_1 := level_1_value; level_2 := level_2_value; level_3 := level_3_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End MwcbDeclineLevelMessage.

  Module MwcbStatusMessage.

    (** Informs data recipients when a MWCB has breached one of the established levels. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      breached_level : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (breached_level record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (breached_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (breached_level_value, bytes) =>
                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; breached_level := breached_level_value |}, bytes)
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

  End MwcbStatusMessage.

  Module IpoQuotingPeriodUpdateMessage.

    (** Indicates the anticipated IPO quotation release time of a security. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      ipo_quotation_release_time : N;
      ipo_quotation_release_qualifier : list byte;
      ipo_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      (ipo_quotation_release_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ipo_quotation_release_qualifier record) = 1 /\
      (ipo_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (ipo_quotation_release_time record) ++
      encode_bytes 1 (ipo_quotation_release_qualifier record) ++
      encode_uint 8 (ipo_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ipo_quotation_release_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (ipo_quotation_release_qualifier_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ipo_price_value, bytes) =>
                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; ipo_quotation_release_time := ipo_quotation_release_time_value; ipo_quotation_release_qualifier := ipo_quotation_release_qualifier_value; ipo_price := ipo_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End IpoQuotingPeriodUpdateMessage.

  Module OperationalHaltMessage.

    (** An Operational Halt means that there has been an interruption of service on the identified security impacting only the designated Market Center. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock_alpha_8 : list byte;
      market_code : list byte;
      operational_halt_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock_alpha_8 record) = 8 /\
      Datatypes.length (market_code record) = 1 /\
      Datatypes.length (operational_halt_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock_alpha_8 record) ++
      encode_bytes 1 (market_code record) ++
      encode_bytes 1 (operational_halt_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_alpha_8_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_code_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (operational_halt_action_value, bytes) =>
                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock_alpha_8 := stock_alpha_8_value; market_code := market_code_value; operational_halt_action := operational_halt_action_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OperationalHaltMessage.

End NsmEquitiesLastSaleTradesFilterViewV402026.
