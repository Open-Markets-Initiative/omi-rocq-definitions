From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Ise Order Feed Market Data

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
  *)

Module IseOptionsOrderFeedV21Server.

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

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; event_code := event_code_value |}, bytes)
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

  Module DerivativeDirectoryMessage.

    (** Derivative Directory Message for active options symbols. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      instrument_id : N;
      security_symbol : list byte;
      expiration_year : N;
      expiration_month : N;
      expiration_day : N;
      explicit_strike_price : N;
      option_type : list byte;
      underlying_symbol : list byte;
      closing_type : list byte;
      tradable : list byte;
      mpv : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_symbol record) = 8 /\
      (expiration_year record < 256 ^ N.of_nat 1)%N /\
      (expiration_month record < 256 ^ N.of_nat 1)%N /\
      (expiration_day record < 256 ^ N.of_nat 1)%N /\
      (explicit_strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (closing_type record) = 1 /\
      Datatypes.length (tradable record) = 1 /\
      Datatypes.length (mpv record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 8 (security_symbol record) ++
      encode_uint 1 (expiration_year record) ++
      encode_uint 1 (expiration_month record) ++
      encode_uint 1 (expiration_day record) ++
      encode_uint 4 (explicit_strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (closing_type record) ++
      encode_bytes 1 (tradable record) ++
      encode_bytes 1 (mpv record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_symbol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (expiration_year_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (expiration_month_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (expiration_day_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (explicit_strike_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (option_type_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (underlying_symbol_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (closing_type_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (tradable_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (mpv_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (reserved_16_value, bytes) =>
                                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; instrument_id := instrument_id_value; security_symbol := security_symbol_value; expiration_year := expiration_year_value; expiration_month := expiration_month_value; expiration_day := expiration_day_value; explicit_strike_price := explicit_strike_price_value; option_type := option_type_value; underlying_symbol := underlying_symbol_value; closing_type := closing_type_value; tradable := tradable_value; mpv := mpv_value; reserved_16 := reserved_16_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativeDirectoryMessage.

  Module TradingActionMessage.

    (** The options system uses this administrative message to indicate the current trading status of an index or equity option within the options market. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      instrument_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (current_trading_state_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; instrument_id := instrument_id_value; current_trading_state := current_trading_state_value |}, bytes)
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

  End TradingActionMessage.

  Module AddOrderMessage.

    (** The Order Message indicates a new order has been accepted and was added to the displayable book. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      instrument_id : N;
      order_reference_number : N;
      side : list byte;
      original_order_volume : N;
      executable_order_volume : N;
      order_status : list byte;
      order_type : list byte;
      order_qualifier : list byte;
      limit_price : N;
      all_or_none : list byte;
      time_in_force : list byte;
      order_capacity : list byte;
      open_close_indicator : list byte;
      owner_id : list byte;
      giveup : list byte;
      cmta : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (original_order_volume record < 256 ^ N.of_nat 4)%N /\
      (executable_order_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_status record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (order_qualifier record) = 1 /\
      (limit_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (all_or_none record) = 1 /\
      Datatypes.length (time_in_force record) = 1 /\
      Datatypes.length (order_capacity record) = 1 /\
      Datatypes.length (open_close_indicator record) = 1 /\
      Datatypes.length (owner_id record) = 6 /\
      Datatypes.length (giveup record) = 6 /\
      Datatypes.length (cmta record) = 6.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (original_order_volume record) ++
      encode_uint 4 (executable_order_volume record) ++
      encode_bytes 1 (order_status record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 1 (order_qualifier record) ++
      encode_uint 4 (limit_price record) ++
      encode_bytes 1 (all_or_none record) ++
      encode_bytes 1 (time_in_force record) ++
      encode_bytes 1 (order_capacity record) ++
      encode_bytes 1 (open_close_indicator record) ++
      encode_bytes 6 (owner_id record) ++
      encode_bytes 6 (giveup record) ++
      encode_bytes 6 (cmta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_order_volume_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (executable_order_volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_status_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (order_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (order_qualifier_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (limit_price_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (all_or_none_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (time_in_force_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (order_capacity_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (open_close_indicator_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (owner_id_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (giveup_value, bytes) =>
                                                                          match decode_bytes 6 bytes with
                                                                          | None => None
                                                                          | Some (cmta_value, bytes) =>
                                                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; instrument_id := instrument_id_value; order_reference_number := order_reference_number_value; side := side_value; original_order_volume := original_order_volume_value; executable_order_volume := executable_order_volume_value; order_status := order_status_value; order_type := order_type_value; order_qualifier := order_qualifier_value; limit_price := limit_price_value; all_or_none := all_or_none_value; time_in_force := time_in_force_value; order_capacity := order_capacity_value; open_close_indicator := open_close_indicator_value; owner_id := owner_id_value; giveup := giveup_value; cmta := cmta_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module AuctionMessage.

    (** This message is used to announce auctions, including the opening auction. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      instrument_id : N;
      auction_id : N;
      auction_type : list byte;
      auction_duration : N;
      auction_event : list byte;
      quantity : N;
      side : list byte;
      price : N;
      imbalance_volume : N;
      exec_flag : list byte;
      order_capacity : list byte;
      owner_id : list byte;
      giveup : list byte;
      cmta : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (auction_duration record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_event record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (imbalance_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_flag record) = 1 /\
      Datatypes.length (order_capacity record) = 1 /\
      Datatypes.length (owner_id record) = 6 /\
      Datatypes.length (giveup record) = 6 /\
      Datatypes.length (cmta record) = 6 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (auction_duration record) ++
      encode_bytes 1 (auction_event record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (imbalance_volume record) ++
      encode_bytes 1 (exec_flag record) ++
      encode_bytes 1 (order_capacity record) ++
      encode_bytes 6 (owner_id record) ++
      encode_bytes 6 (giveup record) ++
      encode_bytes 6 (cmta record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (auction_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (auction_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (auction_duration_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (auction_event_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (quantity_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (imbalance_volume_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (exec_flag_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (order_capacity_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (owner_id_value, bytes) =>
                                                              match decode_bytes 6 bytes with
                                                              | None => None
                                                              | Some (giveup_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (cmta_value, bytes) =>
                                                                      match decode_bytes 16 bytes with
                                                                      | None => None
                                                                      | Some (reserved_16_value, bytes) =>
                                                                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; instrument_id := instrument_id_value; auction_id := auction_id_value; auction_type := auction_type_value; auction_duration := auction_duration_value; auction_event := auction_event_value; quantity := quantity_value; side := side_value; price := price_value; imbalance_volume := imbalance_volume_value; exec_flag := exec_flag_value; order_capacity := order_capacity_value; owner_id := owner_id_value; giveup := giveup_value; cmta := cmta_value; reserved_16 := reserved_16_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionMessage.

  Module EndOfReplaySequenceMessage.

    (** The End of replay Sequence message reflects the sequence number at the time replay of existing messages is complete. *)
    Record t := {
      end_of_replay_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (end_of_replay_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (end_of_replay_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (end_of_replay_sequence_number_value, bytes) =>
          Some ({| end_of_replay_sequence_number := end_of_replay_sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End EndOfReplaySequenceMessage.

End IseOptionsOrderFeedV21Server.
