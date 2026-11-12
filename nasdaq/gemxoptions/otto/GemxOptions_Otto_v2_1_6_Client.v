From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Ouch to Trade Options

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
      - a run counted by a field

    License: MIT No Attribution
  *)

Module GemxOptionsOttoV216Client.

  Module ClientPacketHeader.

    (** Packet header of a packet sent by the client *)
    Record t := {
      packet_length : N;
      client_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (client_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (client_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (client_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; client_packet_type := client_packet_type_value |}, bytes)
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

  End ClientPacketHeader.

  Module LoginRequestPacket.

    (** The SoupBinTCP client must send a Login Request Packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      username : list byte;
      password : list byte;
      requested_session : list byte;
      requested_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 20 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (requested_session_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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

  End LoginRequestPacket.

  Module NewOrderLongFormMessage.

    (** Long form of the New Order request provides full flexibility of configuring order attributes: *)
    Record t := {
      firm_id : list byte;
      instrument_id : N;
      cl_ord_id : list byte;
      cmta : N;
      clearing_account : list byte;
      occ_account : N;
      cust_acct : list byte;
      preferred_party : list byte;
      alo_inst : list byte;
      iso : list byte;
      side : list byte;
      order_type : list byte;
      price : N;
      quantity : N;
      min_qty : N;
      tif : list byte;
      capacity : list byte;
      auction_type : list byte;
      auction_id : N;
      reserved_1 : N;
      disclosure_mask : N;
      price_protection : list byte;
      display_qty : N;
      display_when : list byte;
      display_method : list byte;
      display_low_qty : N;
      display_high_qty : N;
      position_effect_mask : N;
      stock_leg_short_sale : list byte;
      stock_leg_mpid : list byte;
      stock_capacity : list byte;
      second_reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_account record) = 4 /\
      (occ_account record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cust_acct record) = 10 /\
      Datatypes.length (preferred_party record) = 3 /\
      Datatypes.length (alo_inst record) = 1 /\
      Datatypes.length (iso record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tif record) = 1 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (disclosure_mask record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price_protection record) = 1 /\
      (display_qty record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (display_when record) = 1 /\
      Datatypes.length (display_method record) = 1 /\
      (display_low_qty record < 256 ^ N.of_nat 2)%N /\
      (display_high_qty record < 256 ^ N.of_nat 2)%N /\
      (position_effect_mask record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (stock_leg_short_sale record) = 1 /\
      Datatypes.length (stock_leg_mpid record) = 4 /\
      Datatypes.length (stock_capacity record) = 1 /\
      (second_reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 4 (cmta record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 4 (occ_account record) ++
      encode_bytes 10 (cust_acct record) ++
      encode_bytes 3 (preferred_party record) ++
      encode_bytes 1 (alo_inst record) ++
      encode_bytes 1 (iso record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (min_qty record) ++
      encode_bytes 1 (tif record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 1 (disclosure_mask record) ++
      encode_bytes 1 (price_protection record) ++
      encode_uint 2 (display_qty record) ++
      encode_bytes 1 (display_when record) ++
      encode_bytes 1 (display_method record) ++
      encode_uint 2 (display_low_qty record) ++
      encode_uint 2 (display_high_qty record) ++
      encode_uint 2 (position_effect_mask record) ++
      encode_bytes 1 (stock_leg_short_sale record) ++
      encode_bytes 4 (stock_leg_mpid record) ++
      encode_bytes 1 (stock_capacity record) ++
      encode_uint 1 (second_reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cmta_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (clearing_account_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (occ_account_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (cust_acct_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (preferred_party_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (alo_inst_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (iso_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (order_type_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (quantity_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (min_qty_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (tif_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (capacity_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (auction_type_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (auction_id_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (reserved_1_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (disclosure_mask_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (price_protection_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (display_qty_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (display_when_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (display_method_value, bytes) =>
                                                                                                          match decode_uint 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (display_low_qty_value, bytes) =>
                                                                                                              match decode_uint 2 bytes with
                                                                                                              | None => None
                                                                                                              | Some (display_high_qty_value, bytes) =>
                                                                                                                  match decode_uint 2 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (position_effect_mask_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (stock_leg_short_sale_value, bytes) =>
                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (stock_leg_mpid_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (stock_capacity_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (second_reserved_1_value, bytes) =>
                                                                                                                                      Some ({| firm_id := firm_id_value; instrument_id := instrument_id_value; cl_ord_id := cl_ord_id_value; cmta := cmta_value; clearing_account := clearing_account_value; occ_account := occ_account_value; cust_acct := cust_acct_value; preferred_party := preferred_party_value; alo_inst := alo_inst_value; iso := iso_value; side := side_value; order_type := order_type_value; price := price_value; quantity := quantity_value; min_qty := min_qty_value; tif := tif_value; capacity := capacity_value; auction_type := auction_type_value; auction_id := auction_id_value; reserved_1 := reserved_1_value; disclosure_mask := disclosure_mask_value; price_protection := price_protection_value; display_qty := display_qty_value; display_when := display_when_value; display_method := display_method_value; display_low_qty := display_low_qty_value; display_high_qty := display_high_qty_value; position_effect_mask := position_effect_mask_value; stock_leg_short_sale := stock_leg_short_sale_value; stock_leg_mpid := stock_leg_mpid_value; stock_capacity := stock_capacity_value; second_reserved_1 := second_reserved_1_value |}, bytes)
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
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 96.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 bound_31]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderLongFormMessage.

  Module NewOrderShortFormMessage.

    (** Short format of the New Order request is a compact message (less than 50 bytes) with limited flexibility: *)
    Record t := {
      firm_id : list byte;
      instrument_id : N;
      cl_ord_id : list byte;
      alo_inst : list byte;
      iso : list byte;
      side : list byte;
      order_type : list byte;
      price : N;
      quantity_short : N;
      tif : list byte;
      capacity : list byte;
      auction_type : list byte;
      auction_id : N;
      price_protection : list byte;
      position_effect_mask : N;
      stock_capacity : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (alo_inst record) = 1 /\
      Datatypes.length (iso record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (tif record) = 1 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_protection record) = 1 /\
      (position_effect_mask record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (stock_capacity record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 1 (alo_inst record) ++
      encode_bytes 1 (iso record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 2 (quantity_short record) ++
      encode_bytes 1 (tif record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (auction_id record) ++
      encode_bytes 1 (price_protection record) ++
      encode_uint 2 (position_effect_mask record) ++
      encode_bytes 1 (stock_capacity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (alo_inst_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (iso_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (order_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (quantity_short_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (tif_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (capacity_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (auction_type_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (auction_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (price_protection_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (position_effect_mask_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (stock_capacity_value, bytes) =>
                                                                      Some ({| firm_id := firm_id_value; instrument_id := instrument_id_value; cl_ord_id := cl_ord_id_value; alo_inst := alo_inst_value; iso := iso_value; side := side_value; order_type := order_type_value; price := price_value; quantity_short := quantity_short_value; tif := tif_value; capacity := capacity_value; auction_type := auction_type_value; auction_id := auction_id_value; price_protection := price_protection_value; position_effect_mask := position_effect_mask_value; stock_capacity := stock_capacity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderShortFormMessage.

  Module ReplaceOrderMessage.

    (** Replace Order message is used to modify an existing order for both simple and complex instruments. *)
    Record t := {
      firm_id : list byte;
      orig_cl_ord_id : list byte;
      quantity : N;
      order_type : list byte;
      tif : list byte;
      cust_acct : list byte;
      price_protection : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (tif record) = 1 /\
      Datatypes.length (cust_acct record) = 10 /\
      Datatypes.length (price_protection record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 1 (tif record) ++
      encode_bytes 10 (cust_acct record) ++
      encode_bytes 1 (price_protection record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (orig_cl_ord_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (tif_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (cust_acct_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (price_protection_value, bytes) =>
                                  Some ({| firm_id := firm_id_value; orig_cl_ord_id := orig_cl_ord_id_value; quantity := quantity_value; order_type := order_type_value; tif := tif_value; cust_acct := cust_acct_value; price_protection := price_protection_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplaceOrderMessage.

  Module CancelOrderMessage.

    (** The order to be deleted is identified by the ClOrdId field. If the order cannot be deleted, or cannot be found, the request is rejected. *)
    Record t := {
      firm_id : list byte;
      cl_ord_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_ord_id record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_ord_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_ord_id_value, bytes) =>
              Some ({| firm_id := firm_id_value; cl_ord_id := cl_ord_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End CancelOrderMessage.

  Module MassCancelMessage.

    (** This message is used to mass-delete multiple open orders based on the specified Scope. - If message contains invalid fields request is rejected. *)
    Record t := {
      firm_id : list byte;
      cl_request_id : list byte;
      instrument_type : list byte;
      scope : list byte;
      product_id : N;
      instrument_id : N;
      underlying_symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (scope record) = 1 /\
      (product_id record < 256 ^ N.of_nat 2)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (scope record) ++
      encode_uint 2 (product_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 13 (underlying_symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_request_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (instrument_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (scope_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (product_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_bytes 13 bytes with
                              | None => None
                              | Some (underlying_symbol_value, bytes) =>
                                  Some ({| firm_id := firm_id_value; cl_request_id := cl_request_id_value; instrument_type := instrument_type_value; scope := scope_value; product_id := product_id_value; instrument_id := instrument_id_value; underlying_symbol := underlying_symbol_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelMessage.

  Module NewCrossOrderMessage.

    (** Cross Order message allows specifying two opposite sides to trade against each other. The primary side of the order is exposed in an auction if CrossType is set to A (Auction). *)
    Record t := {
      firm_id : list byte;
      instrument_id : N;
      cross_type : list byte;
      auction_type : list byte;
      auction_alloc_pct : N;
      side : list byte;
      iso : list byte;
      price_protection : list byte;
      effective_time : N;
      disclosure_mask : N;
      primary_cl_ord_id : list byte;
      primary_cmta : N;
      primary_clearing_account : list byte;
      primary_occ_account : N;
      primary_cust_acct : list byte;
      primary_price : N;
      primary_quantity : N;
      primary_capacity : list byte;
      primary_position_effect_mask : N;
      primary_stock_leg_short_sale : list byte;
      primary_stock_leg_mpid : list byte;
      primary_stock_capacity : list byte;
      contra_cl_ord_id : list byte;
      contra_cmta : N;
      contra_clearing_account : list byte;
      contra_occ_account : N;
      contra_cust_acct : list byte;
      contra_order_type : list byte;
      contra_price : N;
      contra_quantity : N;
      contra_capacity : list byte;
      contra_position_effect_mask : N;
      contra_stock_leg_short_sale : list byte;
      contra_stock_leg_mpid : list byte;
      contra_stock_capacity : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_alloc_pct record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (iso record) = 1 /\
      Datatypes.length (price_protection record) = 1 /\
      (effective_time record < 256 ^ N.of_nat 8)%N /\
      (disclosure_mask record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (primary_cl_ord_id record) = 16 /\
      (primary_cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (primary_clearing_account record) = 4 /\
      (primary_occ_account record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (primary_cust_acct record) = 10 /\
      (primary_price record < 256 ^ N.of_nat 8)%N /\
      (primary_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (primary_capacity record) = 1 /\
      (primary_position_effect_mask record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (primary_stock_leg_short_sale record) = 1 /\
      Datatypes.length (primary_stock_leg_mpid record) = 4 /\
      Datatypes.length (primary_stock_capacity record) = 1 /\
      Datatypes.length (contra_cl_ord_id record) = 16 /\
      (contra_cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (contra_clearing_account record) = 4 /\
      (contra_occ_account record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (contra_cust_acct record) = 10 /\
      Datatypes.length (contra_order_type record) = 1 /\
      (contra_price record < 256 ^ N.of_nat 8)%N /\
      (contra_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (contra_capacity record) = 1 /\
      (contra_position_effect_mask record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (contra_stock_leg_short_sale record) = 1 /\
      Datatypes.length (contra_stock_leg_mpid record) = 4 /\
      Datatypes.length (contra_stock_capacity record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 1 (auction_alloc_pct record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (iso record) ++
      encode_bytes 1 (price_protection record) ++
      encode_uint 8 (effective_time record) ++
      encode_uint 1 (disclosure_mask record) ++
      encode_bytes 16 (primary_cl_ord_id record) ++
      encode_uint 4 (primary_cmta record) ++
      encode_bytes 4 (primary_clearing_account record) ++
      encode_uint 4 (primary_occ_account record) ++
      encode_bytes 10 (primary_cust_acct record) ++
      encode_uint 8 (primary_price record) ++
      encode_uint 4 (primary_quantity record) ++
      encode_bytes 1 (primary_capacity record) ++
      encode_uint 2 (primary_position_effect_mask record) ++
      encode_bytes 1 (primary_stock_leg_short_sale record) ++
      encode_bytes 4 (primary_stock_leg_mpid record) ++
      encode_bytes 1 (primary_stock_capacity record) ++
      encode_bytes 16 (contra_cl_ord_id record) ++
      encode_uint 4 (contra_cmta record) ++
      encode_bytes 4 (contra_clearing_account record) ++
      encode_uint 4 (contra_occ_account record) ++
      encode_bytes 10 (contra_cust_acct record) ++
      encode_bytes 1 (contra_order_type record) ++
      encode_uint 8 (contra_price record) ++
      encode_uint 4 (contra_quantity record) ++
      encode_bytes 1 (contra_capacity record) ++
      encode_uint 2 (contra_position_effect_mask record) ++
      encode_bytes 1 (contra_stock_leg_short_sale record) ++
      encode_bytes 4 (contra_stock_leg_mpid record) ++
      encode_bytes 1 (contra_stock_capacity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (cross_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (auction_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (auction_alloc_pct_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (iso_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (price_protection_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (effective_time_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (disclosure_mask_value, bytes) =>
                                              match decode_bytes 16 bytes with
                                              | None => None
                                              | Some (primary_cl_ord_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (primary_cmta_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (primary_clearing_account_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (primary_occ_account_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (primary_cust_acct_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (primary_price_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (primary_quantity_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (primary_capacity_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (primary_position_effect_mask_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (primary_stock_leg_short_sale_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (primary_stock_leg_mpid_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (primary_stock_capacity_value, bytes) =>
                                                                                              match decode_bytes 16 bytes with
                                                                                              | None => None
                                                                                              | Some (contra_cl_ord_id_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (contra_cmta_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (contra_clearing_account_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (contra_occ_account_value, bytes) =>
                                                                                                              match decode_bytes 10 bytes with
                                                                                                              | None => None
                                                                                                              | Some (contra_cust_acct_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (contra_order_type_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (contra_price_value, bytes) =>
                                                                                                                          match decode_uint 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (contra_quantity_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (contra_capacity_value, bytes) =>
                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (contra_position_effect_mask_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (contra_stock_leg_short_sale_value, bytes) =>
                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (contra_stock_leg_mpid_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (contra_stock_capacity_value, bytes) =>
                                                                                                                                                  Some ({| firm_id := firm_id_value; instrument_id := instrument_id_value; cross_type := cross_type_value; auction_type := auction_type_value; auction_alloc_pct := auction_alloc_pct_value; side := side_value; iso := iso_value; price_protection := price_protection_value; effective_time := effective_time_value; disclosure_mask := disclosure_mask_value; primary_cl_ord_id := primary_cl_ord_id_value; primary_cmta := primary_cmta_value; primary_clearing_account := primary_clearing_account_value; primary_occ_account := primary_occ_account_value; primary_cust_acct := primary_cust_acct_value; primary_price := primary_price_value; primary_quantity := primary_quantity_value; primary_capacity := primary_capacity_value; primary_position_effect_mask := primary_position_effect_mask_value; primary_stock_leg_short_sale := primary_stock_leg_short_sale_value; primary_stock_leg_mpid := primary_stock_leg_mpid_value; primary_stock_capacity := primary_stock_capacity_value; contra_cl_ord_id := contra_cl_ord_id_value; contra_cmta := contra_cmta_value; contra_clearing_account := contra_clearing_account_value; contra_occ_account := contra_occ_account_value; contra_cust_acct := contra_cust_acct_value; contra_order_type := contra_order_type_value; contra_price := contra_price_value; contra_quantity := contra_quantity_value; contra_capacity := contra_capacity_value; contra_position_effect_mask := contra_position_effect_mask_value; contra_stock_leg_short_sale := contra_stock_leg_short_sale_value; contra_stock_leg_mpid := contra_stock_leg_mpid_value; contra_stock_capacity := contra_stock_capacity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 142.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 bound_34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewCrossOrderMessage.

  Module MemberKillSwitchRequestMessage.

    (** The Member Kill Switch Request is used to block ability to enter new orders, alter existing orders, delete orders, and create complex instruments on MRX. *)
    Record t := {
      firm_id : list byte;
      cl_request_id : list byte;
      target_firm_id : list byte;
      kill_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (target_firm_id record) = 4 /\
      Datatypes.length (kill_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 4 (target_firm_id record) ++
      encode_bytes 1 (kill_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_request_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (target_firm_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (kill_action_value, bytes) =>
                      Some ({| firm_id := firm_id_value; cl_request_id := cl_request_id_value; target_firm_id := target_firm_id_value; kill_action := kill_action_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End MemberKillSwitchRequestMessage.

  Module SubscriptionRequestMessage.

    (** OTTO protocol specifies a number of notification message types that can be sent to the client optionally. *)
    Record t := {
      firm_id : list byte;
      cl_request_id : list byte;
      subscription : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (subscription record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 16 (subscription record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (firm_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (cl_request_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (subscription_value, bytes) =>
                  Some ({| firm_id := firm_id_value; cl_request_id := cl_request_id_value; subscription := subscription_value |}, bytes)
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

  End SubscriptionRequestMessage.

End GemxOptionsOttoV216Client.
