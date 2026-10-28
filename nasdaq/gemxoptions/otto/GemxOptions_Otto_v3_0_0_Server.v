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
  *)

Module GemxOptionsOttoV300Server.

  Module ServerPacketHeader.

    (** Packet header of a packet sent by the server *)
    Record t := {
      packet_length : N;
      server_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (server_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (server_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (server_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; server_packet_type := server_packet_type_value |}, bytes)
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

  End ServerPacketHeader.

  Module LoginAcceptedPacket.

    (** The SoupBinTCP server sends a Login Accepted Packet in response to receiving a valid Login Request from the client *)
    Record t := {
      accepted_session : list byte;
      accepted_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (accepted_session record) = 10 /\
      Datatypes.length (accepted_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (accepted_session record) ++
      encode_bytes 20 (accepted_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (accepted_session_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (accepted_sequence_number_value, bytes) =>
              Some ({| accepted_session := accepted_session_value; accepted_sequence_number := accepted_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End LoginAcceptedPacket.

  Module LoginRejectedPacket.

    (** The SoupBinTCP server sends this packet in response to an invalid Login Request Packet from the client *)
    Record t := {
      reject_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_reason_code_value, bytes) =>
          Some ({| reject_reason_code := reject_reason_code_value |}, bytes)
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

  End LoginRejectedPacket.

  Module SystemEventMessage.

    (** System Event message informs of a market or a session-level event. *)
    Record t := {
      timestamp : N;
      event_code : list byte;
      version : N;
      sub_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1 /\
      (version record < 256 ^ N.of_nat 1)%N /\
      (sub_version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 1 (version record) ++
      encode_uint 1 (sub_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (version_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (sub_version_value, bytes) =>
                      Some ({| timestamp := timestamp_value; event_code := event_code_value; version := version_value; sub_version := sub_version_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module SimpleInstrumentDirectoryMessage.

    (** At the start of each trading day and during intra-day market state changes, the system disseminates directory messages for all symbols trading on the system. *)
    Record t := {
      timestamp : N;
      product_id : N;
      product_name : list byte;
      instrument_id : N;
      expir_year : N;
      expir_mon : N;
      expir_day : N;
      strike_price : N;
      option_type : list byte;
      closing_type : list byte;
      tradable : list byte;
      closing_only : list byte;
      contract_size : N;
      mpv : list byte;
      security_symbol : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (product_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (product_name record) = 13 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (expir_year record < 256 ^ N.of_nat 1)%N /\
      (expir_mon record < 256 ^ N.of_nat 1)%N /\
      (expir_day record < 256 ^ N.of_nat 1)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (closing_type record) = 1 /\
      Datatypes.length (tradable record) = 1 /\
      Datatypes.length (closing_only record) = 1 /\
      (contract_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (mpv record) = 1 /\
      Datatypes.length (security_symbol record) = 8 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (product_id record) ++
      encode_bytes 13 (product_name record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (expir_year record) ++
      encode_uint 1 (expir_mon record) ++
      encode_uint 1 (expir_day record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 1 (closing_type record) ++
      encode_bytes 1 (tradable record) ++
      encode_bytes 1 (closing_only record) ++
      encode_uint 2 (contract_size record) ++
      encode_bytes 1 (mpv record) ++
      encode_bytes 8 (security_symbol record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (product_name_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (expir_year_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (expir_mon_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (expir_day_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (strike_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (option_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (closing_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (tradable_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (closing_only_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (contract_size_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (mpv_value, bytes) =>
                                                              match decode_bytes 8 bytes with
                                                              | None => None
                                                              | Some (security_symbol_value, bytes) =>
                                                                  match decode_bytes 16 bytes with
                                                                  | None => None
                                                                  | Some (reserved_16_value, bytes) =>
                                                                      Some ({| timestamp := timestamp_value; product_id := product_id_value; product_name := product_name_value; instrument_id := instrument_id_value; expir_year := expir_year_value; expir_mon := expir_mon_value; expir_day := expir_day_value; strike_price := strike_price_value; option_type := option_type_value; closing_type := closing_type_value; tradable := tradable_value; closing_only := closing_only_value; contract_size := contract_size_value; mpv := mpv_value; security_symbol := security_symbol_value; reserved_16 := reserved_16_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleInstrumentDirectoryMessage.

  Module InstrumentTradingActionMessage.

    (** This message notifies of changes to the trading status of an instrument. *)
    Record t := {
      timestamp : N;
      product_id : N;
      instrument_id : N;
      trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (product_id record < 256 ^ N.of_nat 2)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (product_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_state_value, bytes) =>
                      Some ({| timestamp := timestamp_value; product_id := product_id_value; instrument_id := instrument_id_value; trading_state := trading_state_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentTradingActionMessage.

  Module OrderAcceptedShortFormMessage.

    (** This message is used to acknowledge a valid order submitted via New Order (Short Form). *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      instrument_id : N;
      order_id : N;
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
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
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
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (order_id record) ++
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
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
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
                                                                              Some ({| timestamp := timestamp_value; firm_id := firm_id_value; instrument_id := instrument_id_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; alo_inst := alo_inst_value; iso := iso_value; side := side_value; order_type := order_type_value; price := price_value; quantity_short := quantity_short_value; tif := tif_value; capacity := capacity_value; auction_type := auction_type_value; auction_id := auction_id_value; price_protection := price_protection_value; position_effect_mask := position_effect_mask_value; stock_capacity := stock_capacity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAcceptedShortFormMessage.

  Module OrderReplacedMessage.

    (** Acknowledges a Replace Order request. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      instrument_id : N;
      orig_order_id : N;
      order_id : N;
      orig_cl_ord_id : list byte;
      cl_ord_id : list byte;
      alo_inst : list byte;
      iso : list byte;
      side : list byte;
      order_type : list byte;
      price : N;
      quantity : N;
      tif : list byte;
      cust_acct : list byte;
      capacity : list byte;
      auction_type : list byte;
      auction_id : N;
      position_effect_mask : N;
      price_protection : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (orig_order_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (orig_cl_ord_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (alo_inst record) = 1 /\
      Datatypes.length (iso record) = 1 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tif record) = 1 /\
      Datatypes.length (cust_acct record) = 10 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (position_effect_mask record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (price_protection record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (orig_order_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (orig_cl_ord_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 1 (alo_inst record) ++
      encode_bytes 1 (iso record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (tif record) ++
      encode_bytes 10 (cust_acct record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 2 (position_effect_mask record) ++
      encode_bytes 1 (price_protection record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (orig_order_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (orig_cl_ord_id_value, bytes) =>
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
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (quantity_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (tif_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (cust_acct_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (capacity_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (auction_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (auction_id_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (position_effect_mask_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (price_protection_value, bytes) =>
                                                                                      Some ({| timestamp := timestamp_value; firm_id := firm_id_value; instrument_id := instrument_id_value; orig_order_id := orig_order_id_value; order_id := order_id_value; orig_cl_ord_id := orig_cl_ord_id_value; cl_ord_id := cl_ord_id_value; alo_inst := alo_inst_value; iso := iso_value; side := side_value; order_type := order_type_value; price := price_value; quantity := quantity_value; tif := tif_value; cust_acct := cust_acct_value; capacity := capacity_value; auction_type := auction_type_value; auction_id := auction_id_value; position_effect_mask := position_effect_mask_value; price_protection := price_protection_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderReplacedMessage.

  Module OrderCanceledMessage.

    (** An Order Canceled Message informs you that an order has been fully canceled. This could be acknowledging a Cancel Order Message, or it could be the result of the order being canceled automatically by the system. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      instrument_id : N;
      order_id : N;
      cl_ord_id : list byte;
      cancel_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (cancel_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cancel_reason_value, bytes) =>
                              Some ({| timestamp := timestamp_value; firm_id := firm_id_value; instrument_id := instrument_id_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; cancel_reason := cancel_reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCanceledMessage.

  Module OrderExecutedMessage.

    (** Order Executed message reports an execution of an order for a simple instrument, a complex instrument, or an option or stock leg of a complex order. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      product_id : N;
      ord_exec_type : list byte;
      instrument_id : N;
      leg_instrument_id : N;
      leg_id : N;
      auction_type : list byte;
      order_id : N;
      cl_ord_id : list byte;
      cross_id : N;
      match_id : N;
      side : list byte;
      stock_leg_short_sale : list byte;
      price : N;
      quantity : N;
      liquidity_ind : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (product_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (ord_exec_type record) = 1 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (stock_leg_short_sale record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (liquidity_ind record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 2 (product_id record) ++
      encode_bytes 1 (ord_exec_type record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (leg_instrument_id record) ++
      encode_uint 1 (leg_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (stock_leg_short_sale record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 1 (liquidity_ind record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (ord_exec_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leg_instrument_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (leg_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (auction_type_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (order_id_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (cl_ord_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (cross_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (match_id_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (stock_leg_short_sale_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (price_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (quantity_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (liquidity_ind_value, bytes) =>
                                                                          Some ({| timestamp := timestamp_value; firm_id := firm_id_value; product_id := product_id_value; ord_exec_type := ord_exec_type_value; instrument_id := instrument_id_value; leg_instrument_id := leg_instrument_id_value; leg_id := leg_id_value; auction_type := auction_type_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; cross_id := cross_id_value; match_id := match_id_value; side := side_value; stock_leg_short_sale := stock_leg_short_sale_value; price := price_value; quantity := quantity_value; liquidity_ind := liquidity_ind_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module TradeDetailsMessage.

    (** A Trade Details message contains additional details, specifically clearing information. This message is sent out with a nominal delay after Order Executed message. Trade Busts and Adjustments are made against individual MatchIds; Modify Trade results are reported with TransType B for the original trade and C for the new trades. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      product_id : N;
      ord_exec_type : list byte;
      instrument_id : N;
      leg_instrument_id : N;
      leg_id : N;
      trans_type : list byte;
      event_source : list byte;
      auction_type : list byte;
      order_id : N;
      cl_ord_id : list byte;
      cross_id : N;
      match_id : N;
      ref_match_id : N;
      side : list byte;
      stock_leg_short_sale : list byte;
      price : N;
      quantity : N;
      liquidity_ind : N;
      cmta : N;
      clearing_account : list byte;
      occ_account : N;
      cust_acct : list byte;
      stock_venue : list byte;
      stock_leg_mpid : list byte;
      capacity : list byte;
      open_close : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (product_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (ord_exec_type record) = 1 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trans_type record) = 1 /\
      Datatypes.length (event_source record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N /\
      (ref_match_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (stock_leg_short_sale record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (liquidity_ind record < 256 ^ N.of_nat 1)%N /\
      (cmta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_account record) = 4 /\
      (occ_account record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cust_acct record) = 10 /\
      Datatypes.length (stock_venue record) = 1 /\
      Datatypes.length (stock_leg_mpid record) = 4 /\
      Datatypes.length (capacity record) = 1 /\
      Datatypes.length (open_close record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 2 (product_id record) ++
      encode_bytes 1 (ord_exec_type record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (leg_instrument_id record) ++
      encode_uint 1 (leg_id record) ++
      encode_bytes 1 (trans_type record) ++
      encode_bytes 1 (event_source record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record) ++
      encode_uint 4 (ref_match_id record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (stock_leg_short_sale record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 1 (liquidity_ind record) ++
      encode_uint 4 (cmta record) ++
      encode_bytes 4 (clearing_account record) ++
      encode_uint 4 (occ_account record) ++
      encode_bytes 10 (cust_acct record) ++
      encode_bytes 1 (stock_venue record) ++
      encode_bytes 4 (stock_leg_mpid record) ++
      encode_bytes 1 (capacity record) ++
      encode_bytes 1 (open_close record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (ord_exec_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leg_instrument_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (leg_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trans_type_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (event_source_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (auction_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (order_id_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (cl_ord_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (cross_id_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (match_id_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (ref_match_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (side_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (stock_leg_short_sale_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (price_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (quantity_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (liquidity_ind_value, bytes) =>
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
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (stock_venue_value, bytes) =>
                                                                                                          match decode_bytes 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (stock_leg_mpid_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (capacity_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (open_close_value, bytes) =>
                                                                                                                      Some ({| timestamp := timestamp_value; firm_id := firm_id_value; product_id := product_id_value; ord_exec_type := ord_exec_type_value; instrument_id := instrument_id_value; leg_instrument_id := leg_instrument_id_value; leg_id := leg_id_value; trans_type := trans_type_value; event_source := event_source_value; auction_type := auction_type_value; order_id := order_id_value; cl_ord_id := cl_ord_id_value; cross_id := cross_id_value; match_id := match_id_value; ref_match_id := ref_match_id_value; side := side_value; stock_leg_short_sale := stock_leg_short_sale_value; price := price_value; quantity := quantity_value; liquidity_ind := liquidity_ind_value; cmta := cmta_value; clearing_account := clearing_account_value; occ_account := occ_account_value; cust_acct := cust_acct_value; stock_venue := stock_venue_value; stock_leg_mpid := stock_leg_mpid_value; capacity := capacity_value; open_close := open_close_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 107.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeDetailsMessage.

  Module CrossOrderAcceptedMessage.

    (** Acknowledges a valid New Cross Order. The Primary Side and Contra Side blocks of the document are carried as Primary and Contra prefixed fields. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      instrument_id : N;
      cross_type : list byte;
      auction_type : list byte;
      auction_id : N;
      auction_alloc_pct : N;
      side : list byte;
      iso : list byte;
      price_protection : list byte;
      effective_time : N;
      disclosure_mask : N;
      primary_order_id : N;
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
      contra_order_id : N;
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
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (auction_alloc_pct record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (iso record) = 1 /\
      Datatypes.length (price_protection record) = 1 /\
      (effective_time record < 256 ^ N.of_nat 8)%N /\
      (disclosure_mask record < 256 ^ N.of_nat 1)%N /\
      (primary_order_id record < 256 ^ N.of_nat 8)%N /\
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
      (contra_order_id record < 256 ^ N.of_nat 8)%N /\
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
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 1 (auction_alloc_pct record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (iso record) ++
      encode_bytes 1 (price_protection record) ++
      encode_uint 8 (effective_time record) ++
      encode_uint 1 (disclosure_mask record) ++
      encode_uint 8 (primary_order_id record) ++
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
      encode_uint 8 (contra_order_id record) ++
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
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
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
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (auction_id_value, bytes) =>
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
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (primary_order_id_value, bytes) =>
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
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (contra_order_id_value, bytes) =>
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
                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (reserved_1_value, bytes) =>
                                                                                                                                                              Some ({| timestamp := timestamp_value; firm_id := firm_id_value; instrument_id := instrument_id_value; cross_type := cross_type_value; auction_type := auction_type_value; auction_id := auction_id_value; auction_alloc_pct := auction_alloc_pct_value; side := side_value; iso := iso_value; price_protection := price_protection_value; effective_time := effective_time_value; disclosure_mask := disclosure_mask_value; primary_order_id := primary_order_id_value; primary_cl_ord_id := primary_cl_ord_id_value; primary_cmta := primary_cmta_value; primary_clearing_account := primary_clearing_account_value; primary_occ_account := primary_occ_account_value; primary_cust_acct := primary_cust_acct_value; primary_price := primary_price_value; primary_quantity := primary_quantity_value; primary_capacity := primary_capacity_value; primary_position_effect_mask := primary_position_effect_mask_value; primary_stock_leg_short_sale := primary_stock_leg_short_sale_value; primary_stock_leg_mpid := primary_stock_leg_mpid_value; contra_order_id := contra_order_id_value; contra_cl_ord_id := contra_cl_ord_id_value; contra_cmta := contra_cmta_value; contra_clearing_account := contra_clearing_account_value; contra_occ_account := contra_occ_account_value; contra_cust_acct := contra_cust_acct_value; contra_order_type := contra_order_type_value; contra_price := contra_price_value; contra_quantity := contra_quantity_value; contra_capacity := contra_capacity_value; contra_position_effect_mask := contra_position_effect_mask_value; contra_stock_leg_short_sale := contra_stock_leg_short_sale_value; contra_stock_leg_mpid := contra_stock_leg_mpid_value; reserved_1 := reserved_1_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 169.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 bound_37]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CrossOrderAcceptedMessage.

  Module MemberKillSwitchNotificationMessage.

    (** The Member Kill Switch Notification informs of a Member Kill Switch Request issued by this OTTO account, or a Kill Switch Action (User or System initiated) targeting Firm ID(s) associated with this OTTO account. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      cl_request_id : list byte;
      target_firm_id : list byte;
      kill_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (target_firm_id record) = 4 /\
      Datatypes.length (kill_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 4 (target_firm_id record) ++
      encode_bytes 1 (kill_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
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
                          Some ({| timestamp := timestamp_value; firm_id := firm_id_value; cl_request_id := cl_request_id_value; target_firm_id := target_firm_id_value; kill_action := kill_action_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MemberKillSwitchNotificationMessage.

  Module MassCancelResponseMessage.

    (** Mass Cancel Response is sent out upon completion of processing of a valid Mass Cancel Request. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      cl_request_id : list byte;
      num_canceled : N;
      num_pending : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16 /\
      (num_canceled record < 256 ^ N.of_nat 4)%N /\
      (num_pending record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_uint 4 (num_canceled record) ++
      encode_uint 4 (num_pending record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_request_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (num_canceled_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (num_pending_value, bytes) =>
                          Some ({| timestamp := timestamp_value; firm_id := firm_id_value; cl_request_id := cl_request_id_value; num_canceled := num_canceled_value; num_pending := num_pending_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelResponseMessage.

  Module ModifyTradeResponseMessage.

    (** Modify Trade Response is sent when a valid Modify Trade Request is accepted. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      instrument_id : N;
      cl_request_id : list byte;
      cl_ord_id : list byte;
      cross_id : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cl_request_id record) = 16 /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 16 (cl_request_id record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (cl_request_id_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (cross_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (match_id_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; firm_id := firm_id_value; instrument_id := instrument_id_value; cl_request_id := cl_request_id_value; cl_ord_id := cl_ord_id_value; cross_id := cross_id_value; match_id := match_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyTradeResponseMessage.

  Module SubscriptionResponseMessage.

    (** Subscription Response is sent after a valid Subscription Request has been processed. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      cl_request_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cl_request_id record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_bytes 16 (cl_request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_request_id_value, bytes) =>
                  Some ({| timestamp := timestamp_value; firm_id := firm_id_value; cl_request_id := cl_request_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End SubscriptionResponseMessage.

  Module RejectMessage.

    (** Reject is sent in response to a Request that is deemed invalid. Reject message contains error code explaining the reason for rejection. *)
    Record t := {
      timestamp : N;
      reject_msg_type : list byte;
      cl_ord_id : list byte;
      reject_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reject_msg_type record) = 1 /\
      Datatypes.length (cl_ord_id record) = 16 /\
      (reject_code record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (reject_msg_type record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_uint 2 (reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reject_msg_type_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (reject_code_value, bytes) =>
                      Some ({| timestamp := timestamp_value; reject_msg_type := reject_msg_type_value; cl_ord_id := cl_ord_id_value; reject_code := reject_code_value |}, bytes)
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

  End RejectMessage.

  Module PendingResponseMessage.

    (** A Pending Response is sent by OTTO when a Request cannot be immediately, fully processed or validated, and indicates that the final status of the Request is not yet known (typically, any Request for a pending instrument). It is eventually followed by the Notification associated with the Request or a Reject. *)
    Record t := {
      timestamp : N;
      firm_id : list byte;
      instrument_id : N;
      pending_msg_type : list byte;
      cl_ord_id : list byte;
      pending_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm_id record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (pending_msg_type record) = 1 /\
      Datatypes.length (cl_ord_id record) = 16 /\
      Datatypes.length (pending_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (firm_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (pending_msg_type record) ++
      encode_bytes 16 (cl_ord_id record) ++
      encode_bytes 1 (pending_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (pending_msg_type_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (pending_reason_value, bytes) =>
                              Some ({| timestamp := timestamp_value; firm_id := firm_id_value; instrument_id := instrument_id_value; pending_msg_type := pending_msg_type_value; cl_ord_id := cl_ord_id_value; pending_reason := pending_reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PendingResponseMessage.

End GemxOptionsOttoV300Server.
