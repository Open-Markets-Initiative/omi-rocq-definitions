From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Level 1

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
  *)

Module TsxLevel1V28.

  Module MessageHeader.

    (** Twenty two byte ascii header carried on every Qrtmd message *)
    Record t := {
      message_length : list byte;
      sequence_number : list byte;
      service_identifier : list byte;
      retransmission_identifier : list byte;
      continuation_identifier : list byte;
      message_type : list byte;
      exchange_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_length record) = 4 /\
      Datatypes.length (sequence_number record) = 9 /\
      Datatypes.length (service_identifier record) = 3 /\
      Datatypes.length (retransmission_identifier record) = 1 /\
      Datatypes.length (continuation_identifier record) = 1 /\
      Datatypes.length (message_type record) = 2 /\
      Datatypes.length (exchange_identifier record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (message_length record) ++
      encode_bytes 9 (sequence_number record) ++
      encode_bytes 3 (service_identifier record) ++
      encode_bytes 1 (retransmission_identifier record) ++
      encode_bytes 1 (continuation_identifier record) ++
      encode_bytes 2 (message_type record) ++
      encode_bytes 2 (exchange_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (service_identifier_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (retransmission_identifier_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (continuation_identifier_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (message_type_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (exchange_identifier_value, bytes) =>
                                  Some ({| message_length := message_length_value; sequence_number := sequence_number_value; service_identifier := service_identifier_value; retransmission_identifier := retransmission_identifier_value; continuation_identifier := continuation_identifier_value; message_type := message_type_value; exchange_identifier := exchange_identifier_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End MessageHeader.

  Module TradeMessage.

    (** A trade in an equity on the Tsx or Tsx Venture market. *)
    Record t := {
      symbol : list byte;
      volume : list byte;
      trade_price : list byte;
      buyer_id : list byte;
      seller_id : list byte;
      trade_time_stamp : list byte;
      last_sale : list byte;
      trade_id : list byte;
      cross_type : list byte;
      moc : list byte;
      bypass : list byte;
      opening_trade : list byte;
      settlement_terms : list byte;
      trading_system_time_stamp : list byte;
      listing_market : list byte;
      product_type : list byte;
      trade_date : list byte;
      is_mid_only : list byte;
      is_dark : list byte;
      is_conditional : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (volume record) = 9 /\
      Datatypes.length (trade_price record) = 11 /\
      Datatypes.length (buyer_id record) = 3 /\
      Datatypes.length (seller_id record) = 3 /\
      Datatypes.length (trade_time_stamp record) = 6 /\
      Datatypes.length (last_sale record) = 11 /\
      Datatypes.length (trade_id record) = 9 /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (moc record) = 1 /\
      Datatypes.length (bypass record) = 1 /\
      Datatypes.length (opening_trade record) = 1 /\
      Datatypes.length (settlement_terms record) = 1 /\
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (product_type record) = 1 /\
      Datatypes.length (trade_date record) = 8 /\
      Datatypes.length (is_mid_only record) = 1 /\
      Datatypes.length (is_dark record) = 1 /\
      Datatypes.length (is_conditional record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 9 (volume record) ++
      encode_bytes 11 (trade_price record) ++
      encode_bytes 3 (buyer_id record) ++
      encode_bytes 3 (seller_id record) ++
      encode_bytes 6 (trade_time_stamp record) ++
      encode_bytes 11 (last_sale record) ++
      encode_bytes 9 (trade_id record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (moc record) ++
      encode_bytes 1 (bypass record) ++
      encode_bytes 1 (opening_trade record) ++
      encode_bytes 1 (settlement_terms record) ++
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 1 (product_type record) ++
      encode_bytes 8 (trade_date record) ++
      encode_bytes 1 (is_mid_only record) ++
      encode_bytes 1 (is_dark record) ++
      encode_bytes 1 (is_conditional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (volume_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (trade_price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (buyer_id_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (seller_id_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (trade_time_stamp_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (last_sale_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (trade_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (cross_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (moc_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (bypass_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (opening_trade_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (settlement_terms_value, bytes) =>
                                                          match decode_bytes 23 bytes with
                                                          | None => None
                                                          | Some (trading_system_time_stamp_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (listing_market_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (product_type_value, bytes) =>
                                                                      match decode_bytes 8 bytes with
                                                                      | None => None
                                                                      | Some (trade_date_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (is_mid_only_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (is_dark_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (is_conditional_value, bytes) =>
                                                                                      Some ({| symbol := symbol_value; volume := volume_value; trade_price := trade_price_value; buyer_id := buyer_id_value; seller_id := seller_id_value; trade_time_stamp := trade_time_stamp_value; last_sale := last_sale_value; trade_id := trade_id_value; cross_type := cross_type_value; moc := moc_value; bypass := bypass_value; opening_trade := opening_trade_value; settlement_terms := settlement_terms_value; trading_system_time_stamp := trading_system_time_stamp_value; listing_market := listing_market_value; product_type := product_type_value; trade_date := trade_date_value; is_mid_only := is_mid_only_value; is_dark := is_dark_value; is_conditional := is_conditional_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module SymbolStatusMessage.

    (** Reference information for a symbol trading on the current day. *)
    Record t := {
      symbol : list byte;
      trading_system_time_stamp : list byte;
      exchange_id : list byte;
      cusip : list byte;
      board_lot : list byte;
      currency : list byte;
      face_value : list byte;
      last_sale : list byte;
      moc_eligible : list byte;
      product_type : list byte;
      symbol_name : list byte;
      stock_group : list byte;
      stock_state : list byte;
      listing_market : list byte;
      buy_maximum_quantity : list byte;
      buy_minimum_quantity : list byte;
      sell_maximum_quantity : list byte;
      sell_minimum_quantity : list byte;
      test_symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (exchange_id record) = 3 /\
      Datatypes.length (cusip record) = 12 /\
      Datatypes.length (board_lot record) = 9 /\
      Datatypes.length (currency record) = 1 /\
      Datatypes.length (face_value record) = 9 /\
      Datatypes.length (last_sale record) = 11 /\
      Datatypes.length (moc_eligible record) = 1 /\
      Datatypes.length (product_type record) = 1 /\
      Datatypes.length (symbol_name record) = 40 /\
      Datatypes.length (stock_group record) = 2 /\
      Datatypes.length (stock_state record) = 2 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (buy_maximum_quantity record) = 9 /\
      Datatypes.length (buy_minimum_quantity record) = 9 /\
      Datatypes.length (sell_maximum_quantity record) = 9 /\
      Datatypes.length (sell_minimum_quantity record) = 9 /\
      Datatypes.length (test_symbol record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 3 (exchange_id record) ++
      encode_bytes 12 (cusip record) ++
      encode_bytes 9 (board_lot record) ++
      encode_bytes 1 (currency record) ++
      encode_bytes 9 (face_value record) ++
      encode_bytes 11 (last_sale record) ++
      encode_bytes 1 (moc_eligible record) ++
      encode_bytes 1 (product_type record) ++
      encode_bytes 40 (symbol_name record) ++
      encode_bytes 2 (stock_group record) ++
      encode_bytes 2 (stock_state record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 9 (buy_maximum_quantity record) ++
      encode_bytes 9 (buy_minimum_quantity record) ++
      encode_bytes 9 (sell_maximum_quantity record) ++
      encode_bytes 9 (sell_minimum_quantity record) ++
      encode_bytes 1 (test_symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 23 bytes with
          | None => None
          | Some (trading_system_time_stamp_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (exchange_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (cusip_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (board_lot_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (currency_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (face_value_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (last_sale_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (moc_eligible_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (product_type_value, bytes) =>
                                              match decode_bytes 40 bytes with
                                              | None => None
                                              | Some (symbol_name_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (stock_group_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (stock_state_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (listing_market_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (buy_maximum_quantity_value, bytes) =>
                                                                  match decode_bytes 9 bytes with
                                                                  | None => None
                                                                  | Some (buy_minimum_quantity_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (sell_maximum_quantity_value, bytes) =>
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (sell_minimum_quantity_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (test_symbol_value, bytes) =>
                                                                                  Some ({| symbol := symbol_value; trading_system_time_stamp := trading_system_time_stamp_value; exchange_id := exchange_id_value; cusip := cusip_value; board_lot := board_lot_value; currency := currency_value; face_value := face_value_value; last_sale := last_sale_value; moc_eligible := moc_eligible_value; product_type := product_type_value; symbol_name := symbol_name_value; stock_group := stock_group_value; stock_state := stock_state_value; listing_market := listing_market_value; buy_maximum_quantity := buy_maximum_quantity_value; buy_minimum_quantity := buy_minimum_quantity_value; sell_maximum_quantity := sell_maximum_quantity_value; sell_minimum_quantity := sell_minimum_quantity_value; test_symbol := test_symbol_value |}, bytes)
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
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 164.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolStatusMessage.

  Module MocImbalanceNotificationMessage.

    (** Volume imbalance for a Market On Close eligible symbol, sent every ten seconds from the beginning of the MOC Imbalance session. *)
    Record t := {
      symbol : list byte;
      imbalance_side : list byte;
      imbalance_volume : list byte;
      imbalance_reference_price : list byte;
      paired_volume : list byte;
      market_order_imbalance_volume : list byte;
      market_order_imbalance_side : list byte;
      near_indicative_closing_price : list byte;
      far_indicative_closing_price : list byte;
      price_variation : list byte;
      trading_system_time_stamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (imbalance_side record) = 1 /\
      Datatypes.length (imbalance_volume record) = 9 /\
      Datatypes.length (imbalance_reference_price record) = 11 /\
      Datatypes.length (paired_volume record) = 9 /\
      Datatypes.length (market_order_imbalance_volume record) = 9 /\
      Datatypes.length (market_order_imbalance_side record) = 1 /\
      Datatypes.length (near_indicative_closing_price record) = 11 /\
      Datatypes.length (far_indicative_closing_price record) = 11 /\
      Datatypes.length (price_variation record) = 5 /\
      Datatypes.length (trading_system_time_stamp record) = 23.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 1 (imbalance_side record) ++
      encode_bytes 9 (imbalance_volume record) ++
      encode_bytes 11 (imbalance_reference_price record) ++
      encode_bytes 9 (paired_volume record) ++
      encode_bytes 9 (market_order_imbalance_volume record) ++
      encode_bytes 1 (market_order_imbalance_side record) ++
      encode_bytes 11 (near_indicative_closing_price record) ++
      encode_bytes 11 (far_indicative_closing_price record) ++
      encode_bytes 5 (price_variation record) ++
      encode_bytes 23 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (imbalance_side_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (imbalance_volume_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (imbalance_reference_price_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (paired_volume_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (market_order_imbalance_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (market_order_imbalance_side_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (near_indicative_closing_price_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (far_indicative_closing_price_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (price_variation_value, bytes) =>
                                              match decode_bytes 23 bytes with
                                              | None => None
                                              | Some (trading_system_time_stamp_value, bytes) =>
                                                  Some ({| symbol := symbol_value; imbalance_side := imbalance_side_value; imbalance_volume := imbalance_volume_value; imbalance_reference_price := imbalance_reference_price_value; paired_volume := paired_volume_value; market_order_imbalance_volume := market_order_imbalance_volume_value; market_order_imbalance_side := market_order_imbalance_side_value; near_indicative_closing_price := near_indicative_closing_price_value; far_indicative_closing_price := far_indicative_closing_price_value; price_variation := price_variation_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 102.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MocImbalanceNotificationMessage.

  Module MocPriceMovementDelayMessage.

    (** Transmitted when Price Movement Extension is invoked. *)
    Record t := {
      symbol : list byte;
      trading_system_time_stamp : list byte;
      stock_state : list byte;
      ccp : list byte;
      vwap : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (stock_state record) = 2 /\
      Datatypes.length (ccp record) = 11 /\
      Datatypes.length (vwap record) = 11.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 2 (stock_state record) ++
      encode_bytes 11 (ccp record) ++
      encode_bytes 11 (vwap record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 23 bytes with
          | None => None
          | Some (trading_system_time_stamp_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (stock_state_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (ccp_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (vwap_value, bytes) =>
                          Some ({| symbol := symbol_value; trading_system_time_stamp := trading_system_time_stamp_value; stock_state := stock_state_value; ccp := ccp_value; vwap := vwap_value |}, bytes)
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

  End MocPriceMovementDelayMessage.

  Module StockStateMessage.

    (** A change in the trading state of a stock. *)
    Record t := {
      symbol : list byte;
      trading_system_time_stamp : list byte;
      comment : list byte;
      stock_state : list byte;
      opening_time : list byte;
      listing_market : list byte;
      product_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (comment record) = 40 /\
      Datatypes.length (stock_state record) = 2 /\
      Datatypes.length (opening_time record) = 6 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (product_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 40 (comment record) ++
      encode_bytes 2 (stock_state record) ++
      encode_bytes 6 (opening_time record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 1 (product_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 23 bytes with
          | None => None
          | Some (trading_system_time_stamp_value, bytes) =>
              match decode_bytes 40 bytes with
              | None => None
              | Some (comment_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (stock_state_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (opening_time_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (listing_market_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (product_type_value, bytes) =>
                                  Some ({| symbol := symbol_value; trading_system_time_stamp := trading_system_time_stamp_value; comment := comment_value; stock_state := stock_state_value; opening_time := opening_time_value; listing_market := listing_market_value; product_type := product_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 85.
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

  End StockStateMessage.

  Module QuoteMessage.

    (** Full update quote sent whenever either the bid or the ask has changed. *)
    Record t := {
      symbol : list byte;
      bid_price : list byte;
      bid_size : list byte;
      ask_price : list byte;
      ask_size : list byte;
      trading_system_time_stamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (bid_price record) = 9 /\
      Datatypes.length (bid_size record) = 9 /\
      Datatypes.length (ask_price record) = 9 /\
      Datatypes.length (ask_size record) = 9 /\
      Datatypes.length (trading_system_time_stamp record) = 23.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 9 (bid_price record) ++
      encode_bytes 9 (bid_size record) ++
      encode_bytes 9 (ask_price record) ++
      encode_bytes 9 (ask_size record) ++
      encode_bytes 23 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (bid_price_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (bid_size_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (ask_price_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (ask_size_value, bytes) =>
                          match decode_bytes 23 bytes with
                          | None => None
                          | Some (trading_system_time_stamp_value, bytes) =>
                              Some ({| symbol := symbol_value; bid_price := bid_price_value; bid_size := bid_size_value; ask_price := ask_price_value; ask_size := ask_size_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End QuoteMessage.

  Module GeneralMessage.

    (** Bulletin in textual format. *)
    Record t := {
      trading_system_time_stamp : list byte;
      bulletin_indicator : list byte;
      message_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (bulletin_indicator record) = 1 /\
      Datatypes.length (message_text record) = 80.

    Definition encode (record : t) : list byte :=
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 1 (bulletin_indicator record) ++
      encode_bytes 80 (message_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 23 bytes with
      | None => None
      | Some (trading_system_time_stamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bulletin_indicator_value, bytes) =>
              match decode_bytes 80 bytes with
              | None => None
              | Some (message_text_value, bytes) =>
                  Some ({| trading_system_time_stamp := trading_system_time_stamp_value; bulletin_indicator := bulletin_indicator_value; message_text := message_text_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 104.
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

  End GeneralMessage.

  Module TradeCancellationMessage.

    (** Cancellation of a trade, reducing total volume, value and transactions by the amount of the cancellation. *)
    Record t := {
      symbol : list byte;
      volume : list byte;
      trade_price : list byte;
      buyer_id : list byte;
      seller_id : list byte;
      trade_time_stamp : list byte;
      original_trade_id : list byte;
      last_sale : list byte;
      trading_system_time_stamp : list byte;
      listing_market : list byte;
      product_type : list byte;
      trade_date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (volume record) = 9 /\
      Datatypes.length (trade_price record) = 11 /\
      Datatypes.length (buyer_id record) = 3 /\
      Datatypes.length (seller_id record) = 3 /\
      Datatypes.length (trade_time_stamp record) = 6 /\
      Datatypes.length (original_trade_id record) = 9 /\
      Datatypes.length (last_sale record) = 11 /\
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (product_type record) = 1 /\
      Datatypes.length (trade_date record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 9 (volume record) ++
      encode_bytes 11 (trade_price record) ++
      encode_bytes 3 (buyer_id record) ++
      encode_bytes 3 (seller_id record) ++
      encode_bytes 6 (trade_time_stamp record) ++
      encode_bytes 9 (original_trade_id record) ++
      encode_bytes 11 (last_sale record) ++
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 1 (product_type record) ++
      encode_bytes 8 (trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (volume_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (trade_price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (buyer_id_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (seller_id_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (trade_time_stamp_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (original_trade_id_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (last_sale_value, bytes) =>
                                      match decode_bytes 23 bytes with
                                      | None => None
                                      | Some (trading_system_time_stamp_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (listing_market_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (product_type_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (trade_date_value, bytes) =>
                                                      Some ({| symbol := symbol_value; volume := volume_value; trade_price := trade_price_value; buyer_id := buyer_id_value; seller_id := seller_id_value; trade_time_stamp := trade_time_stamp_value; original_trade_id := original_trade_id_value; last_sale := last_sale_value; trading_system_time_stamp := trading_system_time_stamp_value; listing_market := listing_market_value; product_type := product_type_value; trade_date := trade_date_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 97.
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

  End TradeCancellationMessage.

  Module IndicativePriceMessage.

    (** Indicative Closing Price, calculated and published at sixteen hundred London time on every trading day. *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      indicative_price : list byte;
      price_marker : list byte;
      business_date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (cusip record) = 12 /\
      Datatypes.length (indicative_price record) = 11 /\
      Datatypes.length (price_marker record) = 1 /\
      Datatypes.length (business_date record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 12 (cusip record) ++
      encode_bytes 11 (indicative_price record) ++
      encode_bytes 1 (price_marker record) ++
      encode_bytes 8 (business_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (indicative_price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (price_marker_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (business_date_value, bytes) =>
                          Some ({| symbol := symbol_value; cusip := cusip_value; indicative_price := indicative_price_value; price_marker := price_marker_value; business_date := business_date_value |}, bytes)
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

  End IndicativePriceMessage.

  Module CalculatedOpeningPriceMessage.

    (** Calculated Opening Price, published continuously from seven in the morning until the Tsx market opens. *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      cop : list byte;
      price_marker : list byte;
      trading_system_time_stamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (cusip record) = 12 /\
      Datatypes.length (cop record) = 11 /\
      Datatypes.length (price_marker record) = 1 /\
      Datatypes.length (trading_system_time_stamp record) = 23.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 12 (cusip record) ++
      encode_bytes 11 (cop record) ++
      encode_bytes 1 (price_marker record) ++
      encode_bytes 23 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (cop_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (price_marker_value, bytes) =>
                      match decode_bytes 23 bytes with
                      | None => None
                      | Some (trading_system_time_stamp_value, bytes) =>
                          Some ({| symbol := symbol_value; cusip := cusip_value; cop := cop_value; price_marker := price_marker_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
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

  End CalculatedOpeningPriceMessage.

  Module TsxTsxvClosingPriceMessage.

    (** Closing price of the trading day with the last bid and ask behind it. *)
    Record t := {
      symbol : list byte;
      cusip : list byte;
      tsx_tsxv_closing_price : list byte;
      tsx_tsxv_last_bid : list byte;
      tsx_tsxv_last_ask : list byte;
      business_date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (cusip record) = 12 /\
      Datatypes.length (tsx_tsxv_closing_price record) = 11 /\
      Datatypes.length (tsx_tsxv_last_bid record) = 9 /\
      Datatypes.length (tsx_tsxv_last_ask record) = 9 /\
      Datatypes.length (business_date record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 12 (cusip record) ++
      encode_bytes 11 (tsx_tsxv_closing_price record) ++
      encode_bytes 9 (tsx_tsxv_last_bid record) ++
      encode_bytes 9 (tsx_tsxv_last_ask record) ++
      encode_bytes 8 (business_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (cusip_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (tsx_tsxv_closing_price_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (tsx_tsxv_last_bid_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (tsx_tsxv_last_ask_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (business_date_value, bytes) =>
                              Some ({| symbol := symbol_value; cusip := cusip_value; tsx_tsxv_closing_price := tsx_tsxv_closing_price_value; tsx_tsxv_last_bid := tsx_tsxv_last_bid_value; tsx_tsxv_last_ask := tsx_tsxv_last_ask_value; business_date := business_date_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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

  End TsxTsxvClosingPriceMessage.

  Module MarketStateMessage.

    (** The indication of the current market state for a stock group. *)
    Record t := {
      trading_system_time_stamp : list byte;
      stock_group : list byte;
      market_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (stock_group record) = 2 /\
      Datatypes.length (market_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 2 (stock_group record) ++
      encode_bytes 1 (market_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 23 bytes with
      | None => None
      | Some (trading_system_time_stamp_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (stock_group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_state_value, bytes) =>
                  Some ({| trading_system_time_stamp := trading_system_time_stamp_value; stock_group := stock_group_value; market_state := market_state_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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

  End MarketStateMessage.

  Module TradingTierStatusMessage.

    (** Statistical information on the number of symbols and stock groups for the current trading day, sent at the beginning of each trading day. *)
    Record t := {
      exchange_id : list byte;
      total_number_of_symbols : list byte;
      total_number_of_stock_groups : list byte;
      trading_system_time_stamp : list byte;
      trading_tier_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 3 /\
      Datatypes.length (total_number_of_symbols record) = 5 /\
      Datatypes.length (total_number_of_stock_groups record) = 3 /\
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (trading_tier_id record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (exchange_id record) ++
      encode_bytes 5 (total_number_of_symbols record) ++
      encode_bytes 3 (total_number_of_stock_groups record) ++
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 6 (trading_tier_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (total_number_of_symbols_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (total_number_of_stock_groups_value, bytes) =>
                  match decode_bytes 23 bytes with
                  | None => None
                  | Some (trading_system_time_stamp_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (trading_tier_id_value, bytes) =>
                          Some ({| exchange_id := exchange_id_value; total_number_of_symbols := total_number_of_symbols_value; total_number_of_stock_groups := total_number_of_stock_groups_value; trading_system_time_stamp := trading_system_time_stamp_value; trading_tier_id := trading_tier_id_value |}, bytes)
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

  End TradingTierStatusMessage.

  Module TradeCorrectionMessage.

    (** Correction of a trade already disseminated. *)
    Record t := {
      symbol : list byte;
      volume : list byte;
      trade_price : list byte;
      buyer_id : list byte;
      seller_id : list byte;
      trade_time_stamp : list byte;
      last_sale : list byte;
      trade_id : list byte;
      cross_type : list byte;
      moc : list byte;
      bypass : list byte;
      opening_trade : list byte;
      settlement_terms : list byte;
      original_trade_id : list byte;
      trading_system_time_stamp : list byte;
      listing_market : list byte;
      product_type : list byte;
      trade_date : list byte;
      is_mid_only : list byte;
      is_dark : list byte;
      is_conditional : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (volume record) = 9 /\
      Datatypes.length (trade_price record) = 11 /\
      Datatypes.length (buyer_id record) = 3 /\
      Datatypes.length (seller_id record) = 3 /\
      Datatypes.length (trade_time_stamp record) = 6 /\
      Datatypes.length (last_sale record) = 11 /\
      Datatypes.length (trade_id record) = 9 /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (moc record) = 1 /\
      Datatypes.length (bypass record) = 1 /\
      Datatypes.length (opening_trade record) = 1 /\
      Datatypes.length (settlement_terms record) = 1 /\
      Datatypes.length (original_trade_id record) = 9 /\
      Datatypes.length (trading_system_time_stamp record) = 23 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (product_type record) = 1 /\
      Datatypes.length (trade_date record) = 8 /\
      Datatypes.length (is_mid_only record) = 1 /\
      Datatypes.length (is_dark record) = 1 /\
      Datatypes.length (is_conditional record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 9 (volume record) ++
      encode_bytes 11 (trade_price record) ++
      encode_bytes 3 (buyer_id record) ++
      encode_bytes 3 (seller_id record) ++
      encode_bytes 6 (trade_time_stamp record) ++
      encode_bytes 11 (last_sale record) ++
      encode_bytes 9 (trade_id record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (moc record) ++
      encode_bytes 1 (bypass record) ++
      encode_bytes 1 (opening_trade record) ++
      encode_bytes 1 (settlement_terms record) ++
      encode_bytes 9 (original_trade_id record) ++
      encode_bytes 23 (trading_system_time_stamp record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 1 (product_type record) ++
      encode_bytes 8 (trade_date record) ++
      encode_bytes 1 (is_mid_only record) ++
      encode_bytes 1 (is_dark record) ++
      encode_bytes 1 (is_conditional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (volume_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (trade_price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (buyer_id_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (seller_id_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (trade_time_stamp_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (last_sale_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (trade_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (cross_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (moc_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (bypass_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (opening_trade_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (settlement_terms_value, bytes) =>
                                                          match decode_bytes 9 bytes with
                                                          | None => None
                                                          | Some (original_trade_id_value, bytes) =>
                                                              match decode_bytes 23 bytes with
                                                              | None => None
                                                              | Some (trading_system_time_stamp_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (listing_market_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (product_type_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (trade_date_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (is_mid_only_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (is_dark_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (is_conditional_value, bytes) =>
                                                                                          Some ({| symbol := symbol_value; volume := volume_value; trade_price := trade_price_value; buyer_id := buyer_id_value; seller_id := seller_id_value; trade_time_stamp := trade_time_stamp_value; last_sale := last_sale_value; trade_id := trade_id_value; cross_type := cross_type_value; moc := moc_value; bypass := bypass_value; opening_trade := opening_trade_value; settlement_terms := settlement_terms_value; original_trade_id := original_trade_id_value; trading_system_time_stamp := trading_system_time_stamp_value; listing_market := listing_market_value; product_type := product_type_value; trade_date := trade_date_value; is_mid_only := is_mid_only_value; is_dark := is_dark_value; is_conditional := is_conditional_value |}, bytes)
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
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 114.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

End TsxLevel1V28.
