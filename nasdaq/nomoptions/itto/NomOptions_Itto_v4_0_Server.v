From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Itch To Trade Options

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

Module NomOptionsIttoV40Server.

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

  Module OptionsDirectoryMessage.

    (** At the start of each trading day, NASDAQ disseminates options symbol directory messages for all active options symbols in the NASDAQ option system. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      option_id : N;
      security_symbol : list byte;
      expiration_year : N;
      expiration_month : N;
      expiration_date : N;
      explicit_strike_price : N;
      option_type : list byte;
      source : N;
      underlying_symbol : list byte;
      options_closing_type : list byte;
      tradable : list byte;
      mpv : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_symbol record) = 6 /\
      (expiration_year record < 256 ^ N.of_nat 1)%N /\
      (expiration_month record < 256 ^ N.of_nat 1)%N /\
      (expiration_date record < 256 ^ N.of_nat 1)%N /\
      (explicit_strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 1 /\
      (source record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (options_closing_type record) = 1 /\
      Datatypes.length (tradable record) = 1 /\
      Datatypes.length (mpv record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 6 (security_symbol record) ++
      encode_uint 1 (expiration_year record) ++
      encode_uint 1 (expiration_month record) ++
      encode_uint 1 (expiration_date record) ++
      encode_uint 4 (explicit_strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 1 (source record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (options_closing_type record) ++
      encode_bytes 1 (tradable record) ++
      encode_bytes 1 (mpv record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (option_id_value, bytes) =>
                  match decode_bytes 6 bytes with
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
                              | Some (expiration_date_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (explicit_strike_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (option_type_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (source_value, bytes) =>
                                              match decode_bytes 13 bytes with
                                              | None => None
                                              | Some (underlying_symbol_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (options_closing_type_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (tradable_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (mpv_value, bytes) =>
                                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; option_id := option_id_value; security_symbol := security_symbol_value; expiration_year := expiration_year_value; expiration_month := expiration_month_value; expiration_date := expiration_date_value; explicit_strike_price := explicit_strike_price_value; option_type := option_type_value; source := source_value; underlying_symbol := underlying_symbol_value; options_closing_type := options_closing_type_value; tradable := tradable_value; mpv := mpv_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsDirectoryMessage.

  Module TradingActionMessage.

    (** After the start of system hours, NASDAQ will use the Trading Action message to relay changes in trading status for an individual option. Messages will be sent when an option is halted, is released for quotation, released for trading, or temporarily suspended for trading on the buy or sell side. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      option_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (option_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (current_trading_state_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; option_id := option_id_value; current_trading_state := current_trading_state_value |}, bytes)
                  end
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

  Module SecurityOpenMessage.

    (** NASDAQ plans to disseminate the Option Open Message for each option as soon as the opening is completed. Upon receipt of the open state message, firms should be advised that the option denoted in the message is now available for auto execution within the NASDAQ Options Market System. Upon receipt of the closed state message, firms should be advised that the option is no longer eligible for auto-execution within the NASDAQ Options Market System. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      option_id : N;
      open_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (open_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (option_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (open_state_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; option_id := option_id_value; open_state := open_state_value |}, bytes)
                  end
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

  End SecurityOpenMessage.

  Module AddOrderMessageShortMessageForm.

    (** For bandwidth efficiency reasons, this message can be published in either short or long format. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      market_side : list byte;
      option_id : N;
      price_short : N;
      volume_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_side record) = 1 /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (volume_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (market_side record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 2 (volume_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (option_id_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (price_short_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (volume_short_value, bytes) =>
                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; market_side := market_side_value; option_id := option_id_value; price_short := price_short_value; volume_short := volume_short_value |}, bytes)
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessageShortMessageForm.

  Module AddOrderMessageLongFormMessage.

    (** For bandwidth efficiency reasons, this message can be published in either short or long format. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      market_side : list byte;
      option_id : N;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_side record) = 1 /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (market_side record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (option_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_long_value, bytes) =>
                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; market_side := market_side_value; option_id := option_id_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessageLongFormMessage.

  Module AddQuoteMessageShortFormMessage.

    (** For bandwidth efficiency reasons, this message can be published in either short or long format. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      bid_reference_number : N;
      ask_reference_number : N;
      option_id : N;
      bid_price_short : N;
      bid_size_short : N;
      ask_price_short : N;
      ask_size_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (bid_reference_number record < 256 ^ N.of_nat 8)%N /\
      (ask_reference_number record < 256 ^ N.of_nat 8)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price_short record < 256 ^ N.of_nat 2)%N /\
      (bid_size_short record < 256 ^ N.of_nat 2)%N /\
      (ask_price_short record < 256 ^ N.of_nat 2)%N /\
      (ask_size_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (bid_reference_number record) ++
      encode_uint 8 (ask_reference_number record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 2 (bid_price_short record) ++
      encode_uint 2 (bid_size_short record) ++
      encode_uint 2 (ask_price_short record) ++
      encode_uint 2 (ask_size_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (ask_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (option_id_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (bid_price_short_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (bid_size_short_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ask_price_short_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_size_short_value, bytes) =>
                                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; bid_reference_number := bid_reference_number_value; ask_reference_number := ask_reference_number_value; option_id := option_id_value; bid_price_short := bid_price_short_value; bid_size_short := bid_size_short_value; ask_price_short := ask_price_short_value; ask_size_short := ask_size_short_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End AddQuoteMessageShortFormMessage.

  Module AddQuoteMessageLongFormMessage.

    (** For bandwidth efficiency reasons, this message can be published in either short or long format. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      bid_reference_number : N;
      ask_reference_number : N;
      option_id : N;
      bid : N;
      bid_size_long : N;
      ask : N;
      ask_size_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (bid_reference_number record < 256 ^ N.of_nat 8)%N /\
      (ask_reference_number record < 256 ^ N.of_nat 8)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (bid record < 256 ^ N.of_nat 4)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask record < 256 ^ N.of_nat 4)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (bid_reference_number record) ++
      encode_uint 8 (ask_reference_number record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (bid record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 4 (ask record) ++
      encode_uint 4 (ask_size_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (ask_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (option_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bid_size_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (ask_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (ask_size_long_value, bytes) =>
                                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; bid_reference_number := bid_reference_number_value; ask_reference_number := ask_reference_number_value; option_id := option_id_value; bid := bid_value; bid_size_long := bid_size_long_value; ask := ask_value; ask_size_long := ask_size_long_value |}, bytes)
                                      end
                                  end
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

  End AddQuoteMessageLongFormMessage.

  Module SingleSideExecutedMessage.

    (** This message is sent whenever a Side order is executed in whole or in part. It is possible to receive several Single Side Executed Messages for the same Side order if that Side order is executed in several parts. The multiple Single Side Executed Messages on the same order are cumulative. By combining the executions received separately via two types of Single Side Executed Messages and Trade Messages, it is possible to build a complete view of all non-auction executions that happen on NASDAQ. Auction execution information is available in one bulk print via the Auction Trade Message. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      reference_number : N;
      executed_contracts : N;
      cross_number : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (reference_number record < 256 ^ N.of_nat 8)%N /\
      (executed_contracts record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (reference_number record) ++
      encode_uint 4 (executed_contracts record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (executed_contracts_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (cross_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; reference_number := reference_number_value; executed_contracts := executed_contracts_value; cross_number := cross_number_value; match_number := match_number_value |}, bytes)
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

  End SingleSideExecutedMessage.

  Module SingleSideExecutedWithPriceMessage.

    (** These executions may be marked as non-printable. If the execution is marked as non-printed, it means that the contracts will be included into a later bulk print (e.g., in the case of auction executions). If a firm is looking to use the ITTO data in time-and-sales displays or volume calculations, NASDAQ recommends that firms ignore messages marked as non-printable to prevent double counting. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      reference_number : N;
      cross_number : N;
      match_number : N;
      printable : list byte;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (reference_number record < 256 ^ N.of_nat 8)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (reference_number record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cross_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (printable_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_long_value, bytes) =>
                                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; reference_number := reference_number_value; cross_number := cross_number_value; match_number := match_number_value; printable := printable_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                                  end
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideExecutedWithPriceMessage.

  Module OrderCancelMessage.

    (** This message is sent whenever an order on the book is modified as a result of a partial cancellation. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      cancelled_contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (cancelled_contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (cancelled_contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cancelled_contracts_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; cancelled_contracts := cancelled_contracts_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End OrderCancelMessage.

  Module SingleSideReplaceMessageShortForm.

    (** This message is sent whenever an order or one side of a quote on the book is replaced. The replacement has a new sequence number and replaces the prior sequence number. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      original_reference_number : N;
      new_reference_number : N;
      price_short : N;
      volume_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (original_reference_number record < 256 ^ N.of_nat 8)%N /\
      (new_reference_number record < 256 ^ N.of_nat 8)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (volume_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (original_reference_number record) ++
      encode_uint 8 (new_reference_number record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 2 (volume_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (original_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (new_reference_number_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (price_short_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (volume_short_value, bytes) =>
                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; original_reference_number := original_reference_number_value; new_reference_number := new_reference_number_value; price_short := price_short_value; volume_short := volume_short_value |}, bytes)
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

  End SingleSideReplaceMessageShortForm.

  Module SingleSideReplaceMessageLongForm.

    (** This message is sent whenever an order or one side of a quote on the book is replaced. The replacement has a new sequence number and replaces the prior sequence number. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      original_reference_number : N;
      new_reference_number : N;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (original_reference_number record < 256 ^ N.of_nat 8)%N /\
      (new_reference_number record < 256 ^ N.of_nat 8)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (original_reference_number record) ++
      encode_uint 8 (new_reference_number record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (original_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (new_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_long_value, bytes) =>
                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; original_reference_number := original_reference_number_value; new_reference_number := new_reference_number_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                          end
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

  End SingleSideReplaceMessageLongForm.

  Module SingleSideDeleteMessage.

    (** The message is sent when an order or a side of a quote is being cancelled. All remaining contracts are no longer accessible so the side should be removed from the book. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (reference_number_value, bytes) =>
                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; reference_number := reference_number_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SingleSideDeleteMessage.

  Module SingleSideChangeMessage.

    (** This message is sent whenever an order or a side of a quote is being updated for price and (or) contracts. The reference number associated with the order quote is unchanged. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      reference_number : N;
      change_reason : list byte;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (change_reason record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (reference_number record) ++
      encode_bytes 1 (change_reason record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (change_reason_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_long_value, bytes) =>
                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; reference_number := reference_number_value; change_reason := change_reason_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideChangeMessage.

  Module QuoteReplaceMessageShortForm.

    (** This message is sent whenever a quote on the book is replaced. The replaced quote has new sequence numbers on both sides. These new sequence numbers replace the prior sequence numbers on the quote. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      original_bid_reference_number : N;
      bid_reference_number : N;
      original_ask_reference_number : N;
      ask_reference_number : N;
      bid_price_short : N;
      bid_size_short : N;
      ask_price_short : N;
      ask_size_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (original_bid_reference_number record < 256 ^ N.of_nat 8)%N /\
      (bid_reference_number record < 256 ^ N.of_nat 8)%N /\
      (original_ask_reference_number record < 256 ^ N.of_nat 8)%N /\
      (ask_reference_number record < 256 ^ N.of_nat 8)%N /\
      (bid_price_short record < 256 ^ N.of_nat 2)%N /\
      (bid_size_short record < 256 ^ N.of_nat 2)%N /\
      (ask_price_short record < 256 ^ N.of_nat 2)%N /\
      (ask_size_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (original_bid_reference_number record) ++
      encode_uint 8 (bid_reference_number record) ++
      encode_uint 8 (original_ask_reference_number record) ++
      encode_uint 8 (ask_reference_number record) ++
      encode_uint 2 (bid_price_short record) ++
      encode_uint 2 (bid_size_short record) ++
      encode_uint 2 (ask_price_short record) ++
      encode_uint 2 (ask_size_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (original_bid_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_reference_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_ask_reference_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ask_reference_number_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (bid_price_short_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (bid_size_short_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_price_short_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (ask_size_short_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; original_bid_reference_number := original_bid_reference_number_value; bid_reference_number := bid_reference_number_value; original_ask_reference_number := original_ask_reference_number_value; ask_reference_number := ask_reference_number_value; bid_price_short := bid_price_short_value; bid_size_short := bid_size_short_value; ask_price_short := ask_price_short_value; ask_size_short := ask_size_short_value |}, bytes)
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

  End QuoteReplaceMessageShortForm.

  Module QuoteReplaceMessageLongForm.

    (** This message is sent whenever a quote on the book is replaced. The replaced quote has new sequence numbers on both sides. These new sequence numbers replace the prior sequence numbers on the quote. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      original_bid_reference_number : N;
      bid_reference_number : N;
      original_ask_reference_number : N;
      ask_reference_number : N;
      bid_price_long : N;
      bid_size_long : N;
      ask_price_long : N;
      ask_size_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (original_bid_reference_number record < 256 ^ N.of_nat 8)%N /\
      (bid_reference_number record < 256 ^ N.of_nat 8)%N /\
      (original_ask_reference_number record < 256 ^ N.of_nat 8)%N /\
      (ask_reference_number record < 256 ^ N.of_nat 8)%N /\
      (bid_price_long record < 256 ^ N.of_nat 4)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask_price_long record < 256 ^ N.of_nat 4)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (original_bid_reference_number record) ++
      encode_uint 8 (bid_reference_number record) ++
      encode_uint 8 (original_ask_reference_number record) ++
      encode_uint 8 (ask_reference_number record) ++
      encode_uint 4 (bid_price_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 4 (ask_price_long record) ++
      encode_uint 4 (ask_size_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (original_bid_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_reference_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_ask_reference_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ask_reference_number_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bid_price_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (bid_size_long_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (ask_price_long_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (ask_size_long_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; original_bid_reference_number := original_bid_reference_number_value; bid_reference_number := bid_reference_number_value; original_ask_reference_number := original_ask_reference_number_value; ask_reference_number := ask_reference_number_value; bid_price_long := bid_price_long_value; bid_size_long := bid_size_long_value; ask_price_long := ask_price_long_value; ask_size_long := ask_size_long_value |}, bytes)
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

  End QuoteReplaceMessageLongForm.

  Module QuoteDeleteMessage.

    (** The message is sent when a single quote is being cancelled. All remaining contracts are no longer accessible so the quote should be removed from the book. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      bid_reference_number : N;
      ask_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (bid_reference_number record < 256 ^ N.of_nat 8)%N /\
      (ask_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (bid_reference_number record) ++
      encode_uint 8 (ask_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_reference_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (ask_reference_number_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; bid_reference_number := bid_reference_number_value; ask_reference_number := ask_reference_number_value |}, bytes)
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

  End QuoteDeleteMessage.

  Module OptionsTradeMessagesNonAuction.

    (** This Options Trade Message is designed to provide execution details for normal match events involving non-displayable order types. (Note: There is a separate message for NASDAQ Option auction events.) *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      buy_sell_indicator : list byte;
      option_id : N;
      cross_number : N;
      match_number : N;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (buy_sell_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (option_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (cross_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_long_value, bytes) =>
                                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; buy_sell_indicator := buy_sell_indicator_value; option_id := option_id_value; cross_number := cross_number_value; match_number := match_number_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsTradeMessagesNonAuction.

  Module OptionsCrossTradeMessage.

    (** This message will also be used to report all executions within a price improvement (PRISM) auction. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      option_id : N;
      cross_number : N;
      match_number : N;
      cross_type : list byte;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (option_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cross_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cross_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_long_value, bytes) =>
                                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; option_id := option_id_value; cross_number := cross_number_value; match_number := match_number_value; cross_type := cross_type_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsCrossTradeMessage.

  Module BrokenTradeOrderExecutedMessage.

    (** The Broken Trade Message is sent whenever an execution on NASDAQ is broken. An execution may be broken if it is found to be “clearly erroneous” pursuant to NASDAQ’s Clearly Erroneous Policy. A trade break is final; once a trade is broken, it cannot be reinstated. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      cross_number : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cross_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; cross_number := cross_number_value; match_number := match_number_value |}, bytes)
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

  End BrokenTradeOrderExecutedMessage.

  Module NoiiMessage.

    (** For the NASDAQ Opening Auction, NASDAQ will begin the dissemination of NOII messages for a put or a call option five minutes prior to the start of opening process event and two minutes prior to the halt resumption (reopening) process event. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      auction_id : N;
      auction_type : list byte;
      paired_contracts : N;
      imbalance_direction : list byte;
      option_id : N;
      imbalance_price : N;
      imbalance_volume : N;
      customer_firm_indicator : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (paired_contracts record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (imbalance_direction record) = 1 /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (imbalance_price record < 256 ^ N.of_nat 4)%N /\
      (imbalance_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (customer_firm_indicator record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (auction_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (paired_contracts record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (imbalance_price record) ++
      encode_uint 4 (imbalance_volume record) ++
      encode_bytes 1 (customer_firm_indicator record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (auction_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (paired_contracts_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (imbalance_direction_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (option_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (imbalance_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (imbalance_volume_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (customer_firm_indicator_value, bytes) =>
                                              match decode_uint 3 bytes with
                                              | None => None
                                              | Some (reserved_3_value, bytes) =>
                                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; auction_id := auction_id_value; auction_type := auction_type_value; paired_contracts := paired_contracts_value; imbalance_direction := imbalance_direction_value; option_id := option_id_value; imbalance_price := imbalance_price_value; imbalance_volume := imbalance_volume_value; customer_firm_indicator := customer_firm_indicator_value; reserved_3 := reserved_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NoiiMessage.

End NomOptionsIttoV40Server.
