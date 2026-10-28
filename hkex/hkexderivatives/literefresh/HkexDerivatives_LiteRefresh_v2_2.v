From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Hong Kong Exchanges and Clearing Orion Market Data Derivatives Lite Refresh

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
      - a run counted by a field
  *)

Module HkexDerivativesLiteRefreshV22.

  Module PacketHeader.

    (** Omd packet header (byte 3 is Compression Mode indicator) *)
    Record t := {
      pkt_size : N;
      msg_count : N;
      compression_mode : N;
      seq_num : N;
      send_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pkt_size record < 256 ^ N.of_nat 2)%N /\
      (msg_count record < 256 ^ N.of_nat 1)%N /\
      (compression_mode record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (pkt_size record) ++
      encode_uint 1 (msg_count record) ++
      encode_uint 1 (compression_mode record) ++
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (send_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (pkt_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (compression_mode_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (send_time_value, bytes) =>
                          Some ({| pkt_size := pkt_size_value; msg_count := msg_count_value; compression_mode := compression_mode_value; seq_num := seq_num_value; send_time := send_time_value |}, bytes)
                      end
                  end
              end
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

  End PacketHeader.

  Module MsgHeader.

    (** Omd message header *)
    Record t := {
      msg_size : N;
      msg_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_size record < 256 ^ N.of_nat 2)%N /\
      (msg_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_size record) ++
      encode_uint 2 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_size := msg_size_value; msg_type := msg_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End MsgHeader.

  Module AddOrder.

    (** Generated when a new normal order is inserted into the order book. *)
    Record t := {
      orderbook_id : N;
      order_id : N;
      price : N;
      quantity : N;
      side : N;
      lot_type : N;
      order_type : N;
      order_book_position : N;
      business_time : N;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (lot_type record < 256 ^ N.of_nat 1)%N /\
      (order_type record < 256 ^ N.of_nat 1)%N /\
      (order_book_position record < 256 ^ N.of_nat 4)%N /\
      (business_time record < 256 ^ N.of_nat 8)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (lot_type record) ++
      encode_uint 1 (order_type record) ++
      encode_uint 4 (order_book_position record) ++
      encode_uint 8 (business_time record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (lot_type_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_book_position_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (business_time_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (filler_1_value, bytes) =>
                                              Some ({| orderbook_id := orderbook_id_value; order_id := order_id_value; price := price_value; quantity := quantity_value; side := side_value; lot_type := lot_type_value; order_type := order_type_value; order_book_position := order_book_position_value; business_time := business_time_value; filler_1 := filler_1_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AddOrder.

  Module AggregateImpliedOrder.

    (** Generated whenever there is an update on implied order at the given implied price. *)
    Record t := {
      orderbook_id : N;
      implied_price : N;
      implied_quantity : N;
      side : N;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (implied_price record < 256 ^ N.of_nat 8)%N /\
      (implied_quantity record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 8 (implied_price record) ++
      encode_uint 8 (implied_quantity record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (implied_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (implied_quantity_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (filler_1_value, bytes) =>
                          Some ({| orderbook_id := orderbook_id_value; implied_price := implied_price_value; implied_quantity := implied_quantity_value; side := side_value; filler_1 := filler_1_value |}, bytes)
                      end
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

  End AggregateImpliedOrder.

  Module CalculatedOpeningPriceMessage.

    (** The Calculated Opening Price (COP) message indicates an instrument's theoretical opening price during the pre-opening phases of the market prior to an auction *)
    Record t := {
      orderbook_id : N;
      calculated_opening_price : N;
      filler_4 : N;
      calculated_opening_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (calculated_opening_price record < 256 ^ N.of_nat 8)%N /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      (calculated_opening_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 8 (calculated_opening_price record) ++
      encode_uint 4 (filler_4 record) ++
      encode_uint 8 (calculated_opening_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (calculated_opening_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (filler_4_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (calculated_opening_quantity_value, bytes) =>
                      Some ({| orderbook_id := orderbook_id_value; calculated_opening_price := calculated_opening_price_value; filler_4 := filler_4_value; calculated_opening_quantity := calculated_opening_quantity_value |}, bytes)
                  end
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

  End CalculatedOpeningPriceMessage.

  Module OpenInterestMessage.

    (** Issued to show the Previous Day settlement price and open interest *)
    Record t := {
      day_indicator : N;
      filler_6 : N;
      orderbook_id : N;
      settlement_price : N;
      gross_oi : N;
      net_oi : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (day_indicator record < 256 ^ N.of_nat 2)%N /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      (gross_oi record < 256 ^ N.of_nat 4)%N /\
      (net_oi record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (day_indicator record) ++
      encode_uint 6 (filler_6 record) ++
      encode_uint 4 (orderbook_id record) ++
      encode_uint 8 (settlement_price record) ++
      encode_uint 4 (gross_oi record) ++
      encode_uint 4 (net_oi record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (day_indicator_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (filler_6_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (settlement_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (gross_oi_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (net_oi_value, bytes) =>
                              Some ({| day_indicator := day_indicator_value; filler_6 := filler_6_value; orderbook_id := orderbook_id_value; settlement_price := settlement_price_value; gross_oi := gross_oi_value; net_oi := net_oi_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End OpenInterestMessage.

  Module CommodityDefinition.

    (** Describes individual commodities available from the OMD-D system *)
    Record t := {
      commodity_code : N;
      commodity_name : list byte;
      commodity_id : list byte;
      underlying_code : list byte;
      underlying_type : list byte;
      decimal_in_underlying_price : N;
      base_currency : list byte;
      underlying_issuer : list byte;
      ca_created : list byte;
      effective_tomorrow : N;
      filler_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (commodity_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (commodity_name record) = 40 /\
      Datatypes.length (commodity_id record) = 6 /\
      Datatypes.length (underlying_code record) = 20 /\
      Datatypes.length (underlying_type record) = 1 /\
      (decimal_in_underlying_price record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (base_currency record) = 3 /\
      Datatypes.length (underlying_issuer record) = 6 /\
      Datatypes.length (ca_created record) = 1 /\
      (effective_tomorrow record < 256 ^ N.of_nat 1)%N /\
      (filler_6 record < 256 ^ N.of_nat 6)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (commodity_code record) ++
      encode_bytes 40 (commodity_name record) ++
      encode_bytes 6 (commodity_id record) ++
      encode_bytes 20 (underlying_code record) ++
      encode_bytes 1 (underlying_type record) ++
      encode_uint 1 (decimal_in_underlying_price record) ++
      encode_bytes 3 (base_currency record) ++
      encode_bytes 6 (underlying_issuer record) ++
      encode_bytes 1 (ca_created record) ++
      encode_uint 1 (effective_tomorrow record) ++
      encode_uint 6 (filler_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (commodity_code_value, bytes) =>
          match decode_bytes 40 bytes with
          | None => None
          | Some (commodity_name_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (commodity_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (underlying_code_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (underlying_type_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (decimal_in_underlying_price_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (base_currency_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (underlying_issuer_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (ca_created_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (effective_tomorrow_value, bytes) =>
                                              match decode_uint 6 bytes with
                                              | None => None
                                              | Some (filler_6_value, bytes) =>
                                                  Some ({| commodity_code := commodity_code_value; commodity_name := commodity_name_value; commodity_id := commodity_id_value; underlying_code := underlying_code_value; underlying_type := underlying_type_value; decimal_in_underlying_price := decimal_in_underlying_price_value; base_currency := base_currency_value; underlying_issuer := underlying_issuer_value; ca_created := ca_created_value; effective_tomorrow := effective_tomorrow_value; filler_6 := filler_6_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 89.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CommodityDefinition.

  Module ClassDefinition.

    (** Describes individual instrument classes available from the OMD-D system. *)
    Record t := {
      instrument_class_id : list byte;
      instrument_class_key : N;
      instrument_class_name : list byte;
      exchange : N;
      market : N;
      instrument_group : N;
      modifier : N;
      commodity_code : N;
      filler_3 : N;
      price_quotation_factor : N;
      contract_size : N;
      decimal_in_contract_size : N;
      decimal_in_strike_price : N;
      decimal_in_price : N;
      tick_size : N;
      tradable : N;
      base_currency : list byte;
      settlement_currency_id : list byte;
      effective_tomorrow : N;
      filler_7 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (instrument_class_id record) = 14 /\
      (instrument_class_key record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument_class_name record) = 40 /\
      (exchange record < 256 ^ N.of_nat 2)%N /\
      (market record < 256 ^ N.of_nat 2)%N /\
      (instrument_group record < 256 ^ N.of_nat 2)%N /\
      (modifier record < 256 ^ N.of_nat 1)%N /\
      (commodity_code record < 256 ^ N.of_nat 4)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N /\
      (price_quotation_factor record < 256 ^ N.of_nat 4)%N /\
      (contract_size record < 256 ^ N.of_nat 4)%N /\
      (decimal_in_contract_size record < 256 ^ N.of_nat 1)%N /\
      (decimal_in_strike_price record < 256 ^ N.of_nat 1)%N /\
      (decimal_in_price record < 256 ^ N.of_nat 1)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (tradable record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (base_currency record) = 3 /\
      Datatypes.length (settlement_currency_id record) = 3 /\
      (effective_tomorrow record < 256 ^ N.of_nat 1)%N /\
      (filler_7 record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 14 (instrument_class_id record) ++
      encode_uint 4 (instrument_class_key record) ++
      encode_bytes 40 (instrument_class_name record) ++
      encode_uint 2 (exchange record) ++
      encode_uint 2 (market record) ++
      encode_uint 2 (instrument_group record) ++
      encode_uint 1 (modifier record) ++
      encode_uint 4 (commodity_code record) ++
      encode_uint 3 (filler_3 record) ++
      encode_uint 4 (price_quotation_factor record) ++
      encode_uint 4 (contract_size record) ++
      encode_uint 1 (decimal_in_contract_size record) ++
      encode_uint 1 (decimal_in_strike_price record) ++
      encode_uint 1 (decimal_in_price record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 1 (tradable record) ++
      encode_bytes 3 (base_currency record) ++
      encode_bytes 3 (settlement_currency_id record) ++
      encode_uint 1 (effective_tomorrow record) ++
      encode_uint 7 (filler_7 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 14 bytes with
      | None => None
      | Some (instrument_class_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_class_key_value, bytes) =>
              match decode_bytes 40 bytes with
              | None => None
              | Some (instrument_class_name_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (exchange_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (market_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (instrument_group_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (modifier_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (commodity_code_value, bytes) =>
                                      match decode_uint 3 bytes with
                                      | None => None
                                      | Some (filler_3_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (price_quotation_factor_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (contract_size_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (decimal_in_contract_size_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (decimal_in_strike_price_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (decimal_in_price_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (tick_size_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (tradable_value, bytes) =>
                                                                      match decode_bytes 3 bytes with
                                                                      | None => None
                                                                      | Some (base_currency_value, bytes) =>
                                                                          match decode_bytes 3 bytes with
                                                                          | None => None
                                                                          | Some (settlement_currency_id_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (effective_tomorrow_value, bytes) =>
                                                                                  match decode_uint 7 bytes with
                                                                                  | None => None
                                                                                  | Some (filler_7_value, bytes) =>
                                                                                      Some ({| instrument_class_id := instrument_class_id_value; instrument_class_key := instrument_class_key_value; instrument_class_name := instrument_class_name_value; exchange := exchange_value; market := market_value; instrument_group := instrument_group_value; modifier := modifier_value; commodity_code := commodity_code_value; filler_3 := filler_3_value; price_quotation_factor := price_quotation_factor_value; contract_size := contract_size_value; decimal_in_contract_size := decimal_in_contract_size_value; decimal_in_strike_price := decimal_in_strike_price_value; decimal_in_price := decimal_in_price_value; tick_size := tick_size_value; tradable := tradable_value; base_currency := base_currency_value; settlement_currency_id := settlement_currency_id_value; effective_tomorrow := effective_tomorrow_value; filler_7 := filler_7_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 106.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
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
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClassDefinition.

  Module InstrumentDefinition.

    (** Describes instrument static data. *)
    Record t := {
      orderbook_id : N;
      symbol : list byte;
      instrument_class_key : N;
      exchange : N;
      market : N;
      instrument_group : N;
      modifier : N;
      commodity_code : N;
      last_trading_date : N;
      strike_price : N;
      filler_3 : N;
      date_time_last_trading : N;
      effective_last_trading_date : N;
      date_time_first_trading : N;
      instrument_status_code : N;
      decimal_in_strike_price : N;
      decimal_in_price : N;
      financial_product : list byte;
      put_or_call : N;
      instrument_contract_size : N;
      instrument_price_quotation_factor : N;
      number_of_legs : N;
      vcm_flag : N;
      isin_code : list byte;
      effective_tomorrow : N;
      filler_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 32 /\
      (instrument_class_key record < 256 ^ N.of_nat 4)%N /\
      (exchange record < 256 ^ N.of_nat 2)%N /\
      (market record < 256 ^ N.of_nat 2)%N /\
      (instrument_group record < 256 ^ N.of_nat 2)%N /\
      (modifier record < 256 ^ N.of_nat 1)%N /\
      (commodity_code record < 256 ^ N.of_nat 4)%N /\
      (last_trading_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N /\
      (date_time_last_trading record < 256 ^ N.of_nat 8)%N /\
      (effective_last_trading_date record < 256 ^ N.of_nat 4)%N /\
      (date_time_first_trading record < 256 ^ N.of_nat 8)%N /\
      (instrument_status_code record < 256 ^ N.of_nat 1)%N /\
      (decimal_in_strike_price record < 256 ^ N.of_nat 1)%N /\
      (decimal_in_price record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (financial_product record) = 1 /\
      (put_or_call record < 256 ^ N.of_nat 1)%N /\
      (instrument_contract_size record < 256 ^ N.of_nat 4)%N /\
      (instrument_price_quotation_factor record < 256 ^ N.of_nat 4)%N /\
      (number_of_legs record < 256 ^ N.of_nat 1)%N /\
      (vcm_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (isin_code record) = 12 /\
      (effective_tomorrow record < 256 ^ N.of_nat 1)%N /\
      (filler_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_uint 4 (instrument_class_key record) ++
      encode_uint 2 (exchange record) ++
      encode_uint 2 (market record) ++
      encode_uint 2 (instrument_group record) ++
      encode_uint 1 (modifier record) ++
      encode_uint 4 (commodity_code record) ++
      encode_uint 4 (last_trading_date record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 3 (filler_3 record) ++
      encode_uint 8 (date_time_last_trading record) ++
      encode_uint 4 (effective_last_trading_date record) ++
      encode_uint 8 (date_time_first_trading record) ++
      encode_uint 1 (instrument_status_code record) ++
      encode_uint 1 (decimal_in_strike_price record) ++
      encode_uint 1 (decimal_in_price record) ++
      encode_bytes 1 (financial_product record) ++
      encode_uint 1 (put_or_call record) ++
      encode_uint 4 (instrument_contract_size record) ++
      encode_uint 4 (instrument_price_quotation_factor record) ++
      encode_uint 1 (number_of_legs record) ++
      encode_uint 1 (vcm_flag record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 1 (effective_tomorrow record) ++
      encode_uint 4 (filler_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_class_key_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (exchange_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (market_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (instrument_group_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (modifier_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (commodity_code_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_trading_date_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (strike_price_value, bytes) =>
                                              match decode_uint 3 bytes with
                                              | None => None
                                              | Some (filler_3_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (date_time_last_trading_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (effective_last_trading_date_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (date_time_first_trading_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (instrument_status_code_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (decimal_in_strike_price_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (decimal_in_price_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (financial_product_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (put_or_call_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (instrument_contract_size_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (instrument_price_quotation_factor_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (number_of_legs_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (vcm_flag_value, bytes) =>
                                                                                                  match decode_bytes 12 bytes with
                                                                                                  | None => None
                                                                                                  | Some (isin_code_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (effective_tomorrow_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (filler_4_value, bytes) =>
                                                                                                              Some ({| orderbook_id := orderbook_id_value; symbol := symbol_value; instrument_class_key := instrument_class_key_value; exchange := exchange_value; market := market_value; instrument_group := instrument_group_value; modifier := modifier_value; commodity_code := commodity_code_value; last_trading_date := last_trading_date_value; strike_price := strike_price_value; filler_3 := filler_3_value; date_time_last_trading := date_time_last_trading_value; effective_last_trading_date := effective_last_trading_date_value; date_time_first_trading := date_time_first_trading_value; instrument_status_code := instrument_status_code_value; decimal_in_strike_price := decimal_in_strike_price_value; decimal_in_price := decimal_in_price_value; financial_product := financial_product_value; put_or_call := put_or_call_value; instrument_contract_size := instrument_contract_size_value; instrument_price_quotation_factor := instrument_price_quotation_factor_value; number_of_legs := number_of_legs_value; vcm_flag := vcm_flag_value; isin_code := isin_code_value; effective_tomorrow := effective_tomorrow_value; filler_4 := filler_4_value |}, bytes)
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
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 118.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentDefinition.

  Module CombinationDefinition.

    (** Describes the composition of a combination instrument. *)
    Record t := {
      combo_orderbook_id : N;
      leg_orderbook_id : N;
      filler_3 : N;
      leg_side : list byte;
      leg_ratio : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (combo_orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (leg_orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N /\
      Datatypes.length (leg_side record) = 1 /\
      (leg_ratio record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (combo_orderbook_id record) ++
      encode_uint 4 (leg_orderbook_id record) ++
      encode_uint 3 (filler_3 record) ++
      encode_bytes 1 (leg_side record) ++
      encode_uint 4 (leg_ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (combo_orderbook_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (leg_orderbook_id_value, bytes) =>
              match decode_uint 3 bytes with
              | None => None
              | Some (filler_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (leg_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (leg_ratio_value, bytes) =>
                          Some ({| combo_orderbook_id := combo_orderbook_id_value; leg_orderbook_id := leg_orderbook_id_value; filler_3 := filler_3_value; leg_side := leg_side_value; leg_ratio := leg_ratio_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationDefinition.

  Module RefreshComplete.

    (** RefreshComplete *)
    Record t := {
      last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_seq_num_value, bytes) =>
          Some ({| last_seq_num := last_seq_num_value |}, bytes)
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

  End RefreshComplete.

  Module MarketStatus.

    (** Indicates the state of the Market, Instrument Type, or Class. *)
    Record t := {
      state_level : list byte;
      instrument_class_key : N;
      market : N;
      instrument_group : N;
      commodity_code : N;
      filler_8 : N;
      actual_start_date : list byte;
      actual_start_time : list byte;
      planned_start_date : list byte;
      planned_start_time : list byte;
      trading_session : N;
      state : N;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (state_level record) = 1 /\
      (instrument_class_key record < 256 ^ N.of_nat 4)%N /\
      (market record < 256 ^ N.of_nat 2)%N /\
      (instrument_group record < 256 ^ N.of_nat 2)%N /\
      (commodity_code record < 256 ^ N.of_nat 4)%N /\
      (filler_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (actual_start_date record) = 8 /\
      Datatypes.length (actual_start_time record) = 6 /\
      Datatypes.length (planned_start_date record) = 8 /\
      Datatypes.length (planned_start_time record) = 6 /\
      (trading_session record < 256 ^ N.of_nat 1)%N /\
      (state record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (state_level record) ++
      encode_uint 4 (instrument_class_key record) ++
      encode_uint 2 (market record) ++
      encode_uint 2 (instrument_group record) ++
      encode_uint 4 (commodity_code record) ++
      encode_uint 8 (filler_8 record) ++
      encode_bytes 8 (actual_start_date record) ++
      encode_bytes 6 (actual_start_time record) ++
      encode_bytes 8 (planned_start_date record) ++
      encode_bytes 6 (planned_start_time record) ++
      encode_uint 1 (trading_session record) ++
      encode_uint 2 (state record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (state_level_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_class_key_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (market_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (instrument_group_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (commodity_code_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (filler_8_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (actual_start_date_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (actual_start_time_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (planned_start_date_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (planned_start_time_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (trading_session_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (state_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (filler_2_value, bytes) =>
                                                          Some ({| state_level := state_level_value; instrument_class_key := instrument_class_key_value; market := market_value; instrument_group := instrument_group_value; commodity_code := commodity_code_value; filler_8 := filler_8_value; actual_start_date := actual_start_date_value; actual_start_time := actual_start_time_value; planned_start_date := planned_start_date_value; planned_start_time := planned_start_time_value; trading_session := trading_session_value; state := state_value; filler_2 := filler_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
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
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStatus.

  Module InstrumentStatus.

    (** Generated whenever there is a change to suspension indicator or instrument status. *)
    Record t := {
      orderbook_id : N;
      suspension_indicator : N;
      instrument_status_code : N;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (suspension_indicator record < 256 ^ N.of_nat 1)%N /\
      (instrument_status_code record < 256 ^ N.of_nat 1)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 1 (suspension_indicator record) ++
      encode_uint 1 (instrument_status_code record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (suspension_indicator_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (instrument_status_code_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (filler_2_value, bytes) =>
                      Some ({| orderbook_id := orderbook_id_value; suspension_indicator := suspension_indicator_value; instrument_status_code := instrument_status_code_value; filler_2 := filler_2_value |}, bytes)
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

  End InstrumentStatus.

  Module CommodityAndClassStatus.

    (** Generated whenever a commodity and / or instrument class status changes. *)
    Record t := {
      commodity_code : N;
      instrument_class_key : N;
      suspended : list byte;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (commodity_code record < 256 ^ N.of_nat 4)%N /\
      (instrument_class_key record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (suspended record) = 1 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (commodity_code record) ++
      encode_uint 4 (instrument_class_key record) ++
      encode_bytes 1 (suspended record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (commodity_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_class_key_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (suspended_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (filler_1_value, bytes) =>
                      Some ({| commodity_code := commodity_code_value; instrument_class_key := instrument_class_key_value; suspended := suspended_value; filler_1 := filler_1_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CommodityAndClassStatus.

  Module VcmTrigger.

    (** Generated when VCM is triggered on a particular instrument. *)
    Record t := {
      orderbook_id : N;
      cooling_off_start_time : N;
      cooling_off_end_time : N;
      vcm_reference_price : N;
      vcm_lower_price : N;
      vcm_upper_price : N;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (cooling_off_start_time record < 256 ^ N.of_nat 8)%N /\
      (cooling_off_end_time record < 256 ^ N.of_nat 8)%N /\
      (vcm_reference_price record < 256 ^ N.of_nat 8)%N /\
      (vcm_lower_price record < 256 ^ N.of_nat 8)%N /\
      (vcm_upper_price record < 256 ^ N.of_nat 8)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 8 (cooling_off_start_time record) ++
      encode_uint 8 (cooling_off_end_time record) ++
      encode_uint 8 (vcm_reference_price record) ++
      encode_uint 8 (vcm_lower_price record) ++
      encode_uint 8 (vcm_upper_price record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (cooling_off_start_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cooling_off_end_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (vcm_reference_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (vcm_lower_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (vcm_upper_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (filler_2_value, bytes) =>
                                  Some ({| orderbook_id := orderbook_id_value; cooling_off_start_time := cooling_off_start_time_value; cooling_off_end_time := cooling_off_end_time_value; vcm_reference_price := vcm_reference_price_value; vcm_lower_price := vcm_lower_price_value; vcm_upper_price := vcm_upper_price_value; filler_2 := filler_2_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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

  End VcmTrigger.

  Module ThmTrigger.

    (** Generated when trading halt is triggered on a particular instrument class. *)
    Record t := {
      instrument_class_key : N;
      market : N;
      instrument_group : N;
      modifier : N;
      commodity_code : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_class_key record < 256 ^ N.of_nat 4)%N /\
      (market record < 256 ^ N.of_nat 2)%N /\
      (instrument_group record < 256 ^ N.of_nat 2)%N /\
      (modifier record < 256 ^ N.of_nat 1)%N /\
      (commodity_code record < 256 ^ N.of_nat 4)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_class_key record) ++
      encode_uint 2 (market record) ++
      encode_uint 2 (instrument_group record) ++
      encode_uint 1 (modifier record) ++
      encode_uint 4 (commodity_code record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_class_key_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (market_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (instrument_group_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (modifier_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (commodity_code_value, bytes) =>
                          match decode_uint 3 bytes with
                          | None => None
                          | Some (filler_3_value, bytes) =>
                              Some ({| instrument_class_key := instrument_class_key_value; market := market_value; instrument_group := instrument_group_value; modifier := modifier_value; commodity_code := commodity_code_value; filler_3 := filler_3_value |}, bytes)
                          end
                      end
                  end
              end
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

  End ThmTrigger.

  Module TradeStatisticsMessage.

    (** Trade information for completed deals *)
    Record t := {
      orderbook_id : N;
      last_price : N;
      session : N;
      open_price : N;
      high_price : N;
      low_price : N;
      trade_report_volume : N;
      turnover : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (session record < 256 ^ N.of_nat 1)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (trade_report_volume record < 256 ^ N.of_nat 8)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 1 (session record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (trade_report_volume record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_price_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (open_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (high_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (low_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_report_volume_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (turnover_value, bytes) =>
                                      match decode_uint 3 bytes with
                                      | None => None
                                      | Some (filler_3_value, bytes) =>
                                          Some ({| orderbook_id := orderbook_id_value; last_price := last_price_value; session := session_value; open_price := open_price_value; high_price := high_price_value; low_price := low_price_value; trade_report_volume := trade_report_volume_value; turnover := turnover_value; filler_3 := filler_3_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TradeStatisticsMessage.

End HkexDerivativesLiteRefreshV22.
