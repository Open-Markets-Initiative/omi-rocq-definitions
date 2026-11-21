From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Nasdaq Basic Canada

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

    License: MIT No Attribution
  *)

Module NasdaqCanadaBasicV16.

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

  Module QuotationMessage.

    (** Combined Quotation Report of the Nasdaq Canada best bid and offer, with size attributed to the CXC and CX2 trading books. *)
    Record t := {
      time_stamp : N;
      stock_symbol : list byte;
      nasdaq_canada_best_bid_price : N;
      nasdaq_canada_best_bid_size : N;
      nasdaq_cxc_best_bid_size : N;
      nasdaq_cx_2_best_bid_size : N;
      nasdaq_canada_best_ask_price : N;
      nasdaq_canada_best_ask_size : N;
      nasdaq_cxc_best_ask_size : N;
      nasdaq_cx_2_best_ask_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (stock_symbol record) = 10 /\
      (nasdaq_canada_best_bid_price record < 256 ^ N.of_nat 8)%N /\
      (nasdaq_canada_best_bid_size record < 256 ^ N.of_nat 4)%N /\
      (nasdaq_cxc_best_bid_size record < 256 ^ N.of_nat 4)%N /\
      (nasdaq_cx_2_best_bid_size record < 256 ^ N.of_nat 4)%N /\
      (nasdaq_canada_best_ask_price record < 256 ^ N.of_nat 8)%N /\
      (nasdaq_canada_best_ask_size record < 256 ^ N.of_nat 4)%N /\
      (nasdaq_cxc_best_ask_size record < 256 ^ N.of_nat 4)%N /\
      (nasdaq_cx_2_best_ask_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 8 (nasdaq_canada_best_bid_price record) ++
      encode_uint 4 (nasdaq_canada_best_bid_size record) ++
      encode_uint 4 (nasdaq_cxc_best_bid_size record) ++
      encode_uint 4 (nasdaq_cx_2_best_bid_size record) ++
      encode_uint 8 (nasdaq_canada_best_ask_price record) ++
      encode_uint 4 (nasdaq_canada_best_ask_size record) ++
      encode_uint 4 (nasdaq_cxc_best_ask_size record) ++
      encode_uint 4 (nasdaq_cx_2_best_ask_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (nasdaq_canada_best_bid_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (nasdaq_canada_best_bid_size_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (nasdaq_cxc_best_bid_size_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (nasdaq_cx_2_best_bid_size_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (nasdaq_canada_best_ask_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (nasdaq_canada_best_ask_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (nasdaq_cxc_best_ask_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (nasdaq_cx_2_best_ask_size_value, bytes) =>
                                              Some ({| time_stamp := time_stamp_value; stock_symbol := stock_symbol_value; nasdaq_canada_best_bid_price := nasdaq_canada_best_bid_price_value; nasdaq_canada_best_bid_size := nasdaq_canada_best_bid_size_value; nasdaq_cxc_best_bid_size := nasdaq_cxc_best_bid_size_value; nasdaq_cx_2_best_bid_size := nasdaq_cx_2_best_bid_size_value; nasdaq_canada_best_ask_price := nasdaq_canada_best_ask_price_value; nasdaq_canada_best_ask_size := nasdaq_canada_best_ask_size_value; nasdaq_cxc_best_ask_size := nasdaq_cxc_best_ask_size_value; nasdaq_cx_2_best_ask_size := nasdaq_cx_2_best_ask_size_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuotationMessage.

  Module SaleConditionModifier.

    (** Sale condition modifier consists of four levels *)
    Record t := {
      sale_condition_modifier_level_1 : list byte;
      sales_condition_modifier_level_2 : list byte;
      sales_condition_modifier_level_3 : list byte;
      sales_condition_modifier_level_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sale_condition_modifier_level_1 record) = 1 /\
      Datatypes.length (sales_condition_modifier_level_2 record) = 1 /\
      Datatypes.length (sales_condition_modifier_level_3 record) = 1 /\
      Datatypes.length (sales_condition_modifier_level_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (sale_condition_modifier_level_1 record) ++
      encode_bytes 1 (sales_condition_modifier_level_2 record) ++
      encode_bytes 1 (sales_condition_modifier_level_3 record) ++
      encode_bytes 1 (sales_condition_modifier_level_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (sale_condition_modifier_level_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sales_condition_modifier_level_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sales_condition_modifier_level_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sales_condition_modifier_level_4_value, bytes) =>
                      Some ({| sale_condition_modifier_level_1 := sale_condition_modifier_level_1_value; sales_condition_modifier_level_2 := sales_condition_modifier_level_2_value; sales_condition_modifier_level_3 := sales_condition_modifier_level_3_value; sales_condition_modifier_level_4 := sales_condition_modifier_level_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleConditionModifier.

  Module TradeReportMessage.

    (** Relays all transactions available from or reported by the three Nasdaq Canada Trading Books for the current business day. *)
    Record t := {
      time_stamp : N;
      originating_market_center_identifier : list byte;
      stock_symbol : list byte;
      trade_number : N;
      trade_price : N;
      trade_size : N;
      broker : list byte;
      contra_broker : list byte;
      sale_condition_modifier : SaleConditionModifier.t;
      consolidated_trade_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (stock_symbol record) = 10 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3 /\
      SaleConditionModifier.bounded (sale_condition_modifier record) /\
      (consolidated_trade_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_size record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record) ++
      SaleConditionModifier.encode (sale_condition_modifier record) ++
      encode_uint 8 (consolidated_trade_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (originating_market_center_identifier_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (stock_symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_size_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (broker_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (contra_broker_value, bytes) =>
                                      match SaleConditionModifier.decode bytes with
                                      | None => None
                                      | Some (sale_condition_modifier_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (consolidated_trade_volume_value, bytes) =>
                                              Some ({| time_stamp := time_stamp_value; originating_market_center_identifier := originating_market_center_identifier_value; stock_symbol := stock_symbol_value; trade_number := trade_number_value; trade_price := trade_price_value; trade_size := trade_size_value; broker := broker_value; contra_broker := contra_broker_value; sale_condition_modifier := sale_condition_modifier_value; consolidated_trade_volume := consolidated_trade_volume_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !SaleConditionModifier.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite SaleConditionModifier.decode_encode by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditionModifier.eq_dec]. Defined.

  End TradeReportMessage.

  Module TradeBreakMessage.

    (** Sent if a Trade is cancelled during the same day as its execution. *)
    Record t := {
      time_stamp : N;
      trade_control_number : N;
      originating_market_center_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      (trade_control_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (originating_market_center_identifier record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_uint 4 (trade_control_number record) ++
      encode_bytes 1 (originating_market_center_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_control_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (originating_market_center_identifier_value, bytes) =>
                  Some ({| time_stamp := time_stamp_value; trade_control_number := trade_control_number_value; originating_market_center_identifier := originating_market_center_identifier_value |}, bytes)
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

  End TradeBreakMessage.

  Module TradeCorrectionMessage.

    (** Sent if a Trade is corrected during the same day as its execution. *)
    Record t := {
      time_stamp : N;
      originating_market_center_identifier : list byte;
      stock_symbol : list byte;
      original_trade_number : N;
      original_trade_price : N;
      original_trade_size : N;
      corrected_trade_price : N;
      corrected_trade_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (stock_symbol record) = 10 /\
      (original_trade_number record < 256 ^ N.of_nat 4)%N /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      (corrected_trade_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 4 (original_trade_number record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 4 (original_trade_size record) ++
      encode_uint 8 (corrected_trade_price record) ++
      encode_uint 4 (corrected_trade_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (originating_market_center_identifier_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (stock_symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_trade_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (corrected_trade_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (corrected_trade_size_value, bytes) =>
                                      Some ({| time_stamp := time_stamp_value; originating_market_center_identifier := originating_market_center_identifier_value; stock_symbol := stock_symbol_value; original_trade_number := original_trade_number_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_size := corrected_trade_size_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module SystemEventMessage.

    (** Issued to indicate a market state event. *)
    Record t := {
      time_stamp : N;
      originating_market_center_identifier : list byte;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (originating_market_center_identifier record) = 1 /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 1 (originating_market_center_identifier record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (originating_market_center_identifier_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| time_stamp := time_stamp_value; originating_market_center_identifier := originating_market_center_identifier_value; event_code := event_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End SystemEventMessage.

  Module StockDirectoryMessage.

    (** Disseminated at the start of each trading day for all active symbols in the Nasdaq Execution system. *)
    Record t := {
      time_stamp : N;
      stock_symbol : list byte;
      stock_display_name : list byte;
      listing_market : list byte;
      board_lot_size : list byte;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (stock_symbol record) = 10 /\
      Datatypes.length (stock_display_name record) = 40 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (board_lot_size record) = 4 /\
      Datatypes.length (currency record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_bytes 40 (stock_display_name record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 4 (board_lot_size record) ++
      encode_bytes 1 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_bytes 40 bytes with
              | None => None
              | Some (stock_display_name_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (listing_market_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (board_lot_size_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (currency_value, bytes) =>
                              Some ({| time_stamp := time_stamp_value; stock_symbol := stock_symbol_value; stock_display_name := stock_display_name_value; listing_market := listing_market_value; board_lot_size := board_lot_size_value; currency := currency_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockDirectoryMessage.

  Module StockStatusMessage.

    (** Indicates the current trading status of a stock. *)
    Record t := {
      time_stamp : N;
      stock_symbol : list byte;
      market : list byte;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (stock_symbol record) = 10 /\
      Datatypes.length (market record) = 1 /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_bytes 1 (market record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| time_stamp := time_stamp_value; stock_symbol := stock_symbol_value; market := market_value; system_status := system_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockStatusMessage.

  Module EndOfDayTradeSummaryMessage.

    (** Published once at 4:15PM and again at 5:15PM, including all traded symbols from the day. *)
    Record t := {
      time_stamp : N;
      stock_symbol : list byte;
      consolidated_high_price : N;
      consolidated_low_price : N;
      consolidated_open_price : N;
      listing_center_open_price : N;
      consolidated_close_price : N;
      listing_center_close_price : N;
      consolidated_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (stock_symbol record) = 10 /\
      (consolidated_high_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_low_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_open_price record < 256 ^ N.of_nat 8)%N /\
      (listing_center_open_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_close_price record < 256 ^ N.of_nat 8)%N /\
      (listing_center_close_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 8 (consolidated_high_price record) ++
      encode_uint 8 (consolidated_low_price record) ++
      encode_uint 8 (consolidated_open_price record) ++
      encode_uint 8 (listing_center_open_price record) ++
      encode_uint 8 (consolidated_close_price record) ++
      encode_uint 8 (listing_center_close_price record) ++
      encode_uint 8 (consolidated_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (consolidated_high_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consolidated_low_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (consolidated_open_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (listing_center_open_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (consolidated_close_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (listing_center_close_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (consolidated_volume_value, bytes) =>
                                          Some ({| time_stamp := time_stamp_value; stock_symbol := stock_symbol_value; consolidated_high_price := consolidated_high_price_value; consolidated_low_price := consolidated_low_price_value; consolidated_open_price := consolidated_open_price_value; listing_center_open_price := listing_center_open_price_value; consolidated_close_price := consolidated_close_price_value; listing_center_close_price := listing_center_close_price_value; consolidated_volume := consolidated_volume_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfDayTradeSummaryMessage.

  Module AdjustedClosingPriceMessage.

    (** Previous Day Adjusted Close Price, sent at 7:00AM to reflect any adjustments made overnight. *)
    Record t := {
      time_stamp : N;
      issue_symbol : list byte;
      security_class : list byte;
      adjusted_closing_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_stamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issue_symbol record) = 10 /\
      Datatypes.length (security_class record) = 1 /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_stamp record) ++
      encode_bytes 10 (issue_symbol record) ++
      encode_bytes 1 (security_class record) ++
      encode_uint 8 (adjusted_closing_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (issue_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (security_class_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (adjusted_closing_price_value, bytes) =>
                      Some ({| time_stamp := time_stamp_value; issue_symbol := issue_symbol_value; security_class := security_class_value; adjusted_closing_price := adjusted_closing_price_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AdjustedClosingPriceMessage.

End NasdaqCanadaBasicV16.
