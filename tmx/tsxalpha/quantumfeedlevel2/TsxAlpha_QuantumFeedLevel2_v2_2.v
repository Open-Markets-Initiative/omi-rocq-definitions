From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Quantum Feed Level 2

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
      - a length prefix framing what follows
      - a run counted by a field
  *)

Module TsxAlphaQuantumFeedLevel2V22.

  Module FrameHeader.

    (** Xmt Udp Packet Frame Header *)
    Record t := {
      start_of_frame : N;
      protocol_name : list byte;
      protocol_version : list byte;
      message_length : N;
      session_id : N;
      ack_required_poss_dup : list byte;
      num_body : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_of_frame record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (protocol_name record) = 1 /\
      Datatypes.length (protocol_version record) = 1 /\
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ack_required_poss_dup record) = 1 /\
      (num_body record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (start_of_frame record) ++
      encode_bytes 1 (protocol_name record) ++
      encode_bytes 1 (protocol_version record) ++
      encode_uint 2 (message_length record) ++
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (ack_required_poss_dup record) ++
      encode_uint 1 (num_body record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (start_of_frame_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (protocol_name_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (protocol_version_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (message_length_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (session_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (ack_required_poss_dup_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (num_body_value, bytes) =>
                                  Some ({| start_of_frame := start_of_frame_value; protocol_name := protocol_name_value; protocol_version := protocol_version_value; message_length := message_length_value; session_id := session_id_value; ack_required_poss_dup := ack_required_poss_dup_value; num_body := num_body_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FrameHeader.

  Module BodyHeader.

    (** Xmt Body Header *)
    Record t := {
      msg_length : N;
      msg_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_length record) ++
      encode_bytes 1 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_length := msg_length_value; msg_type := msg_type_value |}, bytes)
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

  End BodyHeader.

  Module BodyHeader2.

    (** Xmt Body Header *)
    Record t := {
      msg_length : N;
      msg_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_length record) ++
      encode_bytes 1 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_length := msg_length_value; msg_type := msg_type_value |}, bytes)
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

  End BodyHeader2.

  Module BusinessHeader.

    (** Xmt Business Header *)
    Record t := {
      msg_version : N;
      source_id : list byte;
      stream_id : N;
      sequence_0 : N;
      sequence_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_version record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (source_id record) = 1 /\
      (stream_id record < 256 ^ N.of_nat 2)%N /\
      (sequence_0 record < 256 ^ N.of_nat 1)%N /\
      (sequence_1 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_version record) ++
      encode_bytes 1 (source_id record) ++
      encode_uint 2 (stream_id record) ++
      encode_uint 1 (sequence_0 record) ++
      encode_uint 4 (sequence_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_version_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (source_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (stream_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sequence_0_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sequence_1_value, bytes) =>
                          Some ({| msg_version := msg_version_value; source_id := source_id_value; stream_id := stream_id_value; sequence_0 := sequence_0_value; sequence_1 := sequence_1_value |}, bytes)
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BusinessHeader.

  Module SymbolStatusMessage.

    Record t := {
      symbol : list byte;
      stock_group : N;
      listing_market : list byte;
      product_type : list byte;
      cusip : list byte;
      board_lot : N;
      currency : list byte;
      face_value : N;
      last_sale : N;
      min_po_qty : N;
      stock_state : list byte;
      test_symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (stock_group record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (product_type record) = 1 /\
      Datatypes.length (cusip record) = 12 /\
      (board_lot record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (currency record) = 1 /\
      (face_value record < 256 ^ N.of_nat 8)%N /\
      (last_sale record < 256 ^ N.of_nat 8)%N /\
      (min_po_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock_state record) = 2 /\
      Datatypes.length (test_symbol record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 1 (stock_group record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 1 (product_type record) ++
      encode_bytes 12 (cusip record) ++
      encode_uint 2 (board_lot record) ++
      encode_bytes 1 (currency record) ++
      encode_uint 8 (face_value record) ++
      encode_uint 8 (last_sale record) ++
      encode_uint 4 (min_po_qty record) ++
      encode_bytes 2 (stock_state record) ++
      encode_bytes 1 (test_symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (stock_group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (listing_market_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (product_type_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (cusip_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (board_lot_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (currency_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (face_value_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_sale_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (min_po_qty_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (stock_state_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (test_symbol_value, bytes) =>
                                                      Some ({| symbol := symbol_value; stock_group := stock_group_value; listing_market := listing_market_value; product_type := product_type_value; cusip := cusip_value; board_lot := board_lot_value; currency := currency_value; face_value := face_value_value; last_sale := last_sale_value; min_po_qty := min_po_qty_value; stock_state := stock_state_value; test_symbol := test_symbol_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolStatusMessage.

  Module OrderBookMessage.

    Record t := {
      symbol : list byte;
      broker_number : N;
      order_side : list byte;
      order_id : N;
      price : N;
      volume : N;
      priority_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (broker_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (priority_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 2 (broker_number record) ++
      encode_bytes 1 (order_side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (priority_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (broker_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (priority_time_stamp_value, bytes) =>
                                  Some ({| symbol := symbol_value; broker_number := broker_number_value; order_side := order_side_value; order_id := order_id_value; price := price_value; volume := volume_value; priority_time_stamp := priority_time_stamp_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookMessage.

  Module MarketStateUpdateMessage.

    Record t := {
      market_state : list byte;
      stock_group : N;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_state record) = 1 /\
      (stock_group record < 256 ^ N.of_nat 1)%N /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_state record) ++
      encode_uint 1 (stock_group record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_state_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (stock_group_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trading_system_time_stamp_value, bytes) =>
                  Some ({| market_state := market_state_value; stock_group := stock_group_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End MarketStateUpdateMessage.

  Module OrderBookedMessage.

    Record t := {
      symbol : list byte;
      broker_number : N;
      order_side : list byte;
      order_id : N;
      price : N;
      volume : N;
      priority_time_stamp : N;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (broker_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (priority_time_stamp record < 256 ^ N.of_nat 8)%N /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 2 (broker_number record) ++
      encode_bytes 1 (order_side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (priority_time_stamp record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (broker_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (priority_time_stamp_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trading_system_time_stamp_value, bytes) =>
                                      Some ({| symbol := symbol_value; broker_number := broker_number_value; order_side := order_side_value; order_id := order_id_value; price := price_value; volume := volume_value; priority_time_stamp := priority_time_stamp_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookedMessage.

  Module OrderCancelledMessage.

    Record t := {
      symbol : list byte;
      broker_number : N;
      order_side : list byte;
      order_id : N;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (broker_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 2 (broker_number record) ++
      encode_bytes 1 (order_side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (broker_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trading_system_time_stamp_value, bytes) =>
                          Some ({| symbol := symbol_value; broker_number := broker_number_value; order_side := order_side_value; order_id := order_id_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelledMessage.

  Module OrderPriceTimeAssignedMessage.

    Record t := {
      symbol : list byte;
      broker_number : N;
      order_side : list byte;
      order_id : N;
      price : N;
      volume : N;
      priority_time_stamp : N;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (broker_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (priority_time_stamp record < 256 ^ N.of_nat 8)%N /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 2 (broker_number record) ++
      encode_bytes 1 (order_side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (priority_time_stamp record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (broker_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (priority_time_stamp_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trading_system_time_stamp_value, bytes) =>
                                      Some ({| symbol := symbol_value; broker_number := broker_number_value; order_side := order_side_value; order_id := order_id_value; price := price_value; volume := volume_value; priority_time_stamp := priority_time_stamp_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderPriceTimeAssignedMessage.

  Module StockStatusMessage.

    Record t := {
      symbol : list byte;
      comment : list byte;
      stock_state : list byte;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (comment record) = 40 /\
      Datatypes.length (stock_state record) = 2 /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_bytes 40 (comment record) ++
      encode_bytes 2 (stock_state record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 40 bytes with
          | None => None
          | Some (comment_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (stock_state_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trading_system_time_stamp_value, bytes) =>
                      Some ({| symbol := symbol_value; comment := comment_value; stock_state := stock_state_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockStatusMessage.

  Module TradeReportMessage.

    Record t := {
      symbol : list byte;
      trade_number : N;
      price : N;
      volume : N;
      buy_broker_number : N;
      buy_order_id : N;
      buy_display_volume : N;
      sell_broker_number : N;
      sell_order_id : N;
      sell_display_volume : N;
      bypass : list byte;
      trade_time_stamp : N;
      cross_type : list byte;
      is_dark : list byte;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (buy_broker_number record < 256 ^ N.of_nat 2)%N /\
      (buy_order_id record < 256 ^ N.of_nat 8)%N /\
      (buy_display_volume record < 256 ^ N.of_nat 4)%N /\
      (sell_broker_number record < 256 ^ N.of_nat 2)%N /\
      (sell_order_id record < 256 ^ N.of_nat 8)%N /\
      (sell_display_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bypass record) = 1 /\
      (trade_time_stamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (is_dark record) = 1 /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 2 (buy_broker_number record) ++
      encode_uint 8 (buy_order_id record) ++
      encode_uint 4 (buy_display_volume record) ++
      encode_uint 2 (sell_broker_number record) ++
      encode_uint 8 (sell_order_id record) ++
      encode_uint 4 (sell_display_volume record) ++
      encode_bytes 1 (bypass record) ++
      encode_uint 4 (trade_time_stamp record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (is_dark record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (buy_broker_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (buy_order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (buy_display_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (sell_broker_number_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (sell_order_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (sell_display_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (bypass_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (trade_time_stamp_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (cross_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (is_dark_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (trading_system_time_stamp_value, bytes) =>
                                                                  Some ({| symbol := symbol_value; trade_number := trade_number_value; price := price_value; volume := volume_value; buy_broker_number := buy_broker_number_value; buy_order_id := buy_order_id_value; buy_display_volume := buy_display_volume_value; sell_broker_number := sell_broker_number_value; sell_order_id := sell_order_id_value; sell_display_volume := sell_display_volume_value; bypass := bypass_value; trade_time_stamp := trade_time_stamp_value; cross_type := cross_type_value; is_dark := is_dark_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeReportMessage.

  Module TradeReportTermsMessage.

    Record t := {
      symbol : list byte;
      trade_number : N;
      price : N;
      volume : N;
      buy_broker_number : N;
      buy_order_id : N;
      buy_display_volume : N;
      sell_broker_number : N;
      sell_order_id : N;
      sell_display_volume : N;
      trade_time_stamp : N;
      settlement_terms : list byte;
      settlement_date : N;
      cross_type : list byte;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (buy_broker_number record < 256 ^ N.of_nat 2)%N /\
      (buy_order_id record < 256 ^ N.of_nat 8)%N /\
      (buy_display_volume record < 256 ^ N.of_nat 4)%N /\
      (sell_broker_number record < 256 ^ N.of_nat 2)%N /\
      (sell_order_id record < 256 ^ N.of_nat 8)%N /\
      (sell_display_volume record < 256 ^ N.of_nat 4)%N /\
      (trade_time_stamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_terms record) = 1 /\
      (settlement_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 2 (buy_broker_number record) ++
      encode_uint 8 (buy_order_id record) ++
      encode_uint 4 (buy_display_volume record) ++
      encode_uint 2 (sell_broker_number record) ++
      encode_uint 8 (sell_order_id record) ++
      encode_uint 4 (sell_display_volume record) ++
      encode_uint 4 (trade_time_stamp record) ++
      encode_bytes 1 (settlement_terms record) ++
      encode_uint 4 (settlement_date record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (buy_broker_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (buy_order_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (buy_display_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (sell_broker_number_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (sell_order_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (sell_display_volume_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (trade_time_stamp_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (settlement_terms_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (settlement_date_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (cross_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (trading_system_time_stamp_value, bytes) =>
                                                                  Some ({| symbol := symbol_value; trade_number := trade_number_value; price := price_value; volume := volume_value; buy_broker_number := buy_broker_number_value; buy_order_id := buy_order_id_value; buy_display_volume := buy_display_volume_value; sell_broker_number := sell_broker_number_value; sell_order_id := sell_order_id_value; sell_display_volume := sell_display_volume_value; trade_time_stamp := trade_time_stamp_value; settlement_terms := settlement_terms_value; settlement_date := settlement_date_value; cross_type := cross_type_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeReportTermsMessage.

  Module TradeCancelledMessage.

    Record t := {
      symbol : list byte;
      trade_number : N;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trading_system_time_stamp_value, bytes) =>
                  Some ({| symbol := symbol_value; trade_number := trade_number_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End TradeCancelledMessage.

  Module TradeCancelledTermsMessage.

    Record t := {
      symbol : list byte;
      trade_number : N;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trading_system_time_stamp_value, bytes) =>
                  Some ({| symbol := symbol_value; trade_number := trade_number_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End TradeCancelledTermsMessage.

  Module TradeCorrectionMessage.

    Record t := {
      symbol : list byte;
      trade_number : N;
      price : N;
      volume : N;
      buy_broker_number : N;
      sell_broker_number : N;
      initiated_by : list byte;
      orig_trade_number : N;
      bypass : list byte;
      trade_time_stamp : N;
      cross_type : list byte;
      is_dark : list byte;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (buy_broker_number record < 256 ^ N.of_nat 2)%N /\
      (sell_broker_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (initiated_by record) = 1 /\
      (orig_trade_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bypass record) = 1 /\
      (trade_time_stamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (is_dark record) = 1 /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 2 (buy_broker_number record) ++
      encode_uint 2 (sell_broker_number record) ++
      encode_bytes 1 (initiated_by record) ++
      encode_uint 4 (orig_trade_number record) ++
      encode_bytes 1 (bypass record) ++
      encode_uint 4 (trade_time_stamp record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (is_dark record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (buy_broker_number_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (sell_broker_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (initiated_by_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (orig_trade_number_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (bypass_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_time_stamp_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cross_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (is_dark_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (trading_system_time_stamp_value, bytes) =>
                                                          Some ({| symbol := symbol_value; trade_number := trade_number_value; price := price_value; volume := volume_value; buy_broker_number := buy_broker_number_value; sell_broker_number := sell_broker_number_value; initiated_by := initiated_by_value; orig_trade_number := orig_trade_number_value; bypass := bypass_value; trade_time_stamp := trade_time_stamp_value; cross_type := cross_type_value; is_dark := is_dark_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module TradeCorrectionTermsMessage.

    Record t := {
      symbol : list byte;
      trade_number : N;
      price : N;
      volume : N;
      buy_broker_number : N;
      sell_broker_number : N;
      initiated_by : list byte;
      orig_trade_number : N;
      trade_time_stamp : N;
      settlement_terms : list byte;
      settlement_date : N;
      cross_type : list byte;
      trading_system_time_stamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 12 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (buy_broker_number record < 256 ^ N.of_nat 2)%N /\
      (sell_broker_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (initiated_by record) = 1 /\
      (orig_trade_number record < 256 ^ N.of_nat 4)%N /\
      (trade_time_stamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_terms record) = 1 /\
      (settlement_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (trading_system_time_stamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 2 (buy_broker_number record) ++
      encode_uint 2 (sell_broker_number record) ++
      encode_bytes 1 (initiated_by record) ++
      encode_uint 4 (orig_trade_number record) ++
      encode_uint 4 (trade_time_stamp record) ++
      encode_bytes 1 (settlement_terms record) ++
      encode_uint 4 (settlement_date record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 8 (trading_system_time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (buy_broker_number_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (sell_broker_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (initiated_by_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (orig_trade_number_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (trade_time_stamp_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (settlement_terms_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (settlement_date_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (cross_type_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (trading_system_time_stamp_value, bytes) =>
                                                          Some ({| symbol := symbol_value; trade_number := trade_number_value; price := price_value; volume := volume_value; buy_broker_number := buy_broker_number_value; sell_broker_number := sell_broker_number_value; initiated_by := initiated_by_value; orig_trade_number := orig_trade_number_value; trade_time_stamp := trade_time_stamp_value; settlement_terms := settlement_terms_value; settlement_date := settlement_date_value; cross_type := cross_type_value; trading_system_time_stamp := trading_system_time_stamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionTermsMessage.

End TsxAlphaQuantumFeedLevel2V22.
