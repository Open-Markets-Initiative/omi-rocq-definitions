From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Express Orders

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
      - a field read in bits
      - a run counted by a field
  *)

Module PearlEquitiesExpressOrdersV27B.

  Module EsesmPacketHeader.

    (** ESesM packet header *)
    Record t := {
      esesm_packet_length : N;
      esesm_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (esesm_packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (esesm_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (esesm_packet_length record) ++
      encode_bytes 1 (esesm_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (esesm_packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (esesm_packet_type_value, bytes) =>
              Some ({| esesm_packet_length := esesm_packet_length_value; esesm_packet_type := esesm_packet_type_value |}, bytes)
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

  End EsesmPacketHeader.

  Module SymbolUpdateMessage.

    (** used to disseminate all security symbols traded on MIAX Pearl Equities for the current session *)
    Record t := {
      matching_engine_time : N;
      symbol_id : N;
      ticker_symbol : list byte;
      reserved_1 : N;
      test_security_indicator : list byte;
      second_reserved_1 : N;
      lot_size : N;
      opening_time : list byte;
      closing_time : list byte;
      primary_market_code : list byte;
      reserved_12 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ticker_symbol record) = 11 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (test_security_indicator record) = 1 /\
      (second_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (opening_time record) = 8 /\
      Datatypes.length (closing_time record) = 8 /\
      Datatypes.length (primary_market_code record) = 1 /\
      Datatypes.length (reserved_12 record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_uint 4 (symbol_id record) ++
      encode_bytes 11 (ticker_symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (test_security_indicator record) ++
      encode_uint 1 (second_reserved_1 record) ++
      encode_uint 4 (lot_size record) ++
      encode_bytes 8 (opening_time record) ++
      encode_bytes 8 (closing_time record) ++
      encode_bytes 1 (primary_market_code record) ++
      encode_bytes 12 (reserved_12 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (ticker_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (test_security_indicator_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (second_reserved_1_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (lot_size_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (opening_time_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (closing_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (primary_market_code_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (reserved_12_value, bytes) =>
                                                  Some ({| matching_engine_time := matching_engine_time_value; symbol_id := symbol_id_value; ticker_symbol := ticker_symbol_value; reserved_1 := reserved_1_value; test_security_indicator := test_security_indicator_value; second_reserved_1 := second_reserved_1_value; lot_size := lot_size_value; opening_time := opening_time_value; closing_time := closing_time_value; primary_market_code := primary_market_code_value; reserved_12 := reserved_12_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
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

  End SymbolUpdateMessage.

  Module NewOrderResponseMessage.

    (** provides an acknowledgement for a New Order Request accepted by MIAX Pearl Equities *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      price : N;
      size : N;
      order_status : list byte;
      reserved_19 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_status record) = 1 /\
      Datatypes.length (reserved_19 record) = 19.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record) ++
      encode_bytes 1 (order_status record) ++
      encode_bytes 19 (reserved_19 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (size_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_status_value, bytes) =>
                                      match decode_bytes 19 bytes with
                                      | None => None
                                      | Some (reserved_19_value, bytes) =>
                                          Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; price := price_value; size := size_value; order_status := order_status_value; reserved_19 := reserved_19_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderResponseMessage.

  Module ModifyOrderResponseMessage.

    (** This message format provides acknowledgement for a Modify Order Request accepted by MIAX Pearl Equities *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      original_client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      leaves_qty : N;
      price : N;
      modify_status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (modify_status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (modify_status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (symbol_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (modify_status_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (reserved_10_value, bytes) =>
                                              Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; price := price_value; modify_status := modify_status_value; reserved_10 := reserved_10_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderResponseMessage.

  Module CancelOrderResponseMessage.

    (** This message format provides response to an Order Cancel Request *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      original_client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      leaves_qty : N;
      cancel_status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cancel_status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (cancel_status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (symbol_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (cancel_status_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (reserved_10_value, bytes) =>
                                          Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; cancel_status := cancel_status_value; reserved_10 := reserved_10_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderResponseMessage.

  Module CancelOrderByExchangeOrderIdResponseMessage.

    (** Cancel Order by Exchange Order ID Response *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      leaves_qty : N;
      cancel_status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cancel_status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (cancel_status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leaves_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cancel_status_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (reserved_10_value, bytes) =>
                                      Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; cancel_status := cancel_status_value; reserved_10 := reserved_10_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderByExchangeOrderIdResponseMessage.

  Module SystemStateNotificationMessage.

    (** This message is published whenever system state events take place *)
    Record t := {
      matching_engine_time : N;
      meo_version : list byte;
      session_id : N;
      system_status : list byte;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (meo_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1 /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 8 (meo_version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (meo_version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (reserved_8_value, bytes) =>
                          Some ({| matching_engine_time := matching_engine_time_value; meo_version := meo_version_value; session_id := session_id_value; system_status := system_status_value; reserved_8 := reserved_8_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemStateNotificationMessage.

  Module CancelReduceSizeOrderNotificationMessage.

    (** This is the message format that will be used when Cancel Order Request is accepted by MIAX Pearl Equities or when unsolicited order cancels or order size reductions are to be notified to firms *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      leaves_qty : N;
      cancel_reason : list byte;
      last_price : N;
      last_size : N;
      pending_cancel_status : list byte;
      pending_reject_reason : list byte;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cancel_reason record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (last_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (pending_cancel_status record) = 1 /\
      Datatypes.length (pending_reject_reason record) = 1 /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (cancel_reason record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 4 (last_size record) ++
      encode_bytes 1 (pending_cancel_status record) ++
      encode_bytes 1 (pending_reject_reason record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leaves_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cancel_reason_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_size_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (pending_cancel_status_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (pending_reject_reason_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (reserved_8_value, bytes) =>
                                                      Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; cancel_reason := cancel_reason_value; last_price := last_price_value; last_size := last_size_value; pending_cancel_status := pending_cancel_status_value; pending_reject_reason := pending_reject_reason_value; reserved_8 := reserved_8_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelReduceSizeOrderNotificationMessage.

  Module OrderPriceUpdateNotificationMessage.

    (** This is the message format that will be used to notify firms about order reprices *)
    Record t := {
      matching_engine_time : N;
      symbol_id : N;
      order_id : N;
      client_order_id : list byte;
      working_price : N;
      nbbo_indicator : list byte;
      reserved_9 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (client_order_id record) = 20 /\
      (working_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (nbbo_indicator record) = 1 /\
      Datatypes.length (reserved_9 record) = 9.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 8 (working_price record) ++
      encode_bytes 1 (nbbo_indicator record) ++
      encode_bytes 9 (reserved_9 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (client_order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (working_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (nbbo_indicator_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (reserved_9_value, bytes) =>
                                  Some ({| matching_engine_time := matching_engine_time_value; symbol_id := symbol_id_value; order_id := order_id_value; client_order_id := client_order_id_value; working_price := working_price_value; nbbo_indicator := nbbo_indicator_value; reserved_9 := reserved_9_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderPriceUpdateNotificationMessage.

  Module ReserveOrderReplenishmentNotificationMessage.

    (** This is the message format that will be used to notify firms of their Reserve order replenishment events *)
    Record t := {
      matching_engine_time : N;
      symbol_id : N;
      order_id : N;
      secondary_order_id : N;
      display_qty : N;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 4 (display_qty record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (secondary_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (display_qty_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (reserved_10_value, bytes) =>
                              Some ({| matching_engine_time := matching_engine_time_value; symbol_id := symbol_id_value; order_id := order_id_value; secondary_order_id := secondary_order_id_value; display_qty := display_qty_value; reserved_10 := reserved_10_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReserveOrderReplenishmentNotificationMessage.

  Module NewOrderResponseMessage2.

    (** provides an acknowledgement for a New Order Request accepted by MIAX Pearl Equities *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      price : N;
      size : N;
      order_status : list byte;
      reserved_19 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_status record) = 1 /\
      Datatypes.length (reserved_19 record) = 19.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record) ++
      encode_bytes 1 (order_status record) ++
      encode_bytes 19 (reserved_19 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (size_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_status_value, bytes) =>
                                      match decode_bytes 19 bytes with
                                      | None => None
                                      | Some (reserved_19_value, bytes) =>
                                          Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; price := price_value; size := size_value; order_status := order_status_value; reserved_19 := reserved_19_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderResponseMessage2.

  Module ModifyOrderResponseMessage2.

    (** This message format provides acknowledgement for a Modify Order Request accepted by MIAX Pearl Equities *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      original_client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      leaves_qty : N;
      price : N;
      modify_status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (modify_status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (modify_status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (symbol_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (modify_status_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (reserved_10_value, bytes) =>
                                              Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; price := price_value; modify_status := modify_status_value; reserved_10 := reserved_10_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderResponseMessage2.

  Module CancelOrderRequestMessage.

    (** Firms can use this format to send a cancel request for a resting order *)
    Record t := {
      reserved_8 : N;
      mpid : list byte;
      client_order_id : list byte;
      original_client_order_id : list byte;
      symbol_id : N;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (reserved_8 record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (reserved_8_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (symbol_id_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (reserved_10_value, bytes) =>
                              Some ({| reserved_8 := reserved_8_value; mpid := mpid_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; symbol_id := symbol_id_value; reserved_10 := reserved_10_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderRequestMessage.

  Module CancelOrderResponseMessage2.

    (** This message format provides response to an Order Cancel Request *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      original_client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      leaves_qty : N;
      cancel_status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (original_client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cancel_status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 20 (original_client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (cancel_status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (original_client_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (symbol_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leaves_qty_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (cancel_status_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (reserved_10_value, bytes) =>
                                          Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; original_client_order_id := original_client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; cancel_status := cancel_status_value; reserved_10 := reserved_10_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderResponseMessage2.

  Module CancelOrderByExchangeOrderIdRequestMessage.

    (** Firms can use this format to send a cancel request for a resting order using Exchange assigned Order ID *)
    Record t := {
      reserved_8 : N;
      mpid : list byte;
      client_order_id : list byte;
      order_id : N;
      symbol_id : N;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (reserved_8 record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (reserved_8_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (symbol_id_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (reserved_10_value, bytes) =>
                              Some ({| reserved_8 := reserved_8_value; mpid := mpid_value; client_order_id := client_order_id_value; order_id := order_id_value; symbol_id := symbol_id_value; reserved_10 := reserved_10_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderByExchangeOrderIdRequestMessage.

  Module CancelOrderByExchangeOrderIdResponseMessage2.

    (** Cancel Order by Exchange Order ID Response *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      symbol_id : N;
      order_id : N;
      leaves_qty : N;
      cancel_status : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cancel_status record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (leaves_qty record) ++
      encode_bytes 1 (cancel_status record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leaves_qty_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cancel_status_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (reserved_10_value, bytes) =>
                                      Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; symbol_id := symbol_id_value; order_id := order_id_value; leaves_qty := leaves_qty_value; cancel_status := cancel_status_value; reserved_10 := reserved_10_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderByExchangeOrderIdResponseMessage2.

  Module MassCancelRequestMessage.

    (** Firms can use this message format to request the cancellation of all orders for an MPID *)
    Record t := {
      reserved_8 : N;
      mpid : list byte;
      client_order_id : list byte;
      scope : list byte;
      action : list byte;
      purge_group : list byte;
      reserved_9 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      Datatypes.length (scope record) = 1 /\
      Datatypes.length (action record) = 1 /\
      Datatypes.length (purge_group record) = 1 /\
      Datatypes.length (reserved_9 record) = 9.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (reserved_8 record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_bytes 1 (scope record) ++
      encode_bytes 1 (action record) ++
      encode_bytes 1 (purge_group record) ++
      encode_bytes 9 (reserved_9 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (reserved_8_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (scope_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (action_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (purge_group_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (reserved_9_value, bytes) =>
                                  Some ({| reserved_8 := reserved_8_value; mpid := mpid_value; client_order_id := client_order_id_value; scope := scope_value; action := action_value; purge_group := purge_group_value; reserved_9 := reserved_9_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
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

  End MassCancelRequestMessage.

  Module AggressiveSidePurgeResponseMessage.

    (** This message format will be used to inform the Firm about the status of their previous ASP Mass Cancel Request *)
    Record t := {
      matching_engine_time : N;
      mpid : list byte;
      client_order_id : list byte;
      symbold_id : N;
      asp_status : list byte;
      number_of_orders_cancelled : N;
      asp_eligible_orders_cancelled : list byte;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (client_order_id record) = 20 /\
      (symbold_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (asp_status record) = 1 /\
      (number_of_orders_cancelled record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (asp_eligible_orders_cancelled record) = 1 /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 20 (client_order_id record) ++
      encode_uint 4 (symbold_id record) ++
      encode_bytes 1 (asp_status record) ++
      encode_uint 1 (number_of_orders_cancelled record) ++
      encode_bytes 1 (asp_eligible_orders_cancelled record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (mpid_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbold_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (asp_status_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (number_of_orders_cancelled_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (asp_eligible_orders_cancelled_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (reserved_10_value, bytes) =>
                                      Some ({| matching_engine_time := matching_engine_time_value; mpid := mpid_value; client_order_id := client_order_id_value; symbold_id := symbold_id_value; asp_status := asp_status_value; number_of_orders_cancelled := number_of_orders_cancelled_value; asp_eligible_orders_cancelled := asp_eligible_orders_cancelled_value; reserved_10 := reserved_10_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AggressiveSidePurgeResponseMessage.

  Module ReserveOrderReplenishmentNotificationMessage2.

    (** This is the message format that will be used to notify firms of their Reserve order replenishment events *)
    Record t := {
      matching_engine_time : N;
      symbol_id : N;
      order_id : N;
      secondary_order_id : N;
      display_qty : N;
      reserved_10 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (matching_engine_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (secondary_order_id record < 256 ^ N.of_nat 8)%N /\
      (display_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_10 record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (matching_engine_time record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (secondary_order_id record) ++
      encode_uint 4 (display_qty record) ++
      encode_bytes 10 (reserved_10 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (matching_engine_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (secondary_order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (display_qty_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (reserved_10_value, bytes) =>
                              Some ({| matching_engine_time := matching_engine_time_value; symbol_id := symbol_id_value; order_id := order_id_value; secondary_order_id := secondary_order_id_value; display_qty := display_qty_value; reserved_10 := reserved_10_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReserveOrderReplenishmentNotificationMessage2.

  Module SynchronizationComplete.

    (** The ESesM server sends a Login response packet in response a Login request packet from the client *)
    Record t := {
      number_of_matching_engines : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_matching_engines record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (number_of_matching_engines record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (number_of_matching_engines_value, bytes) =>
          Some ({| number_of_matching_engines := number_of_matching_engines_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End SynchronizationComplete.

  Module RetransmissionRequest.

    (** The ESesM client uses this packet to request a retransmission server to retransmit a range of packets *)
    Record t := {
      start_sequence_number : N;
      end_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (end_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (start_sequence_number record) ++
      encode_uint 8 (end_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (start_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (end_sequence_number_value, bytes) =>
              Some ({| start_sequence_number := start_sequence_number_value; end_sequence_number := end_sequence_number_value |}, bytes)
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

  End RetransmissionRequest.

End PearlEquitiesExpressOrdersV27B.
