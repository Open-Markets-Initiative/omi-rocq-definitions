From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Itch to Trade Options

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

Module NomOptionsIttoV32Server.

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

  Module SecondsMessage.

    (** Sent every second for which at least one ITTO message is being generated. For bandwidth efficiency the timestamp is separated into this standalone Seconds message and a Nanoseconds portion carried by every other message. *)
    Record t := {
      second : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (second record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (second_value, bytes) =>
          Some ({| second := second_value |}, bytes)
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

  End SecondsMessage.

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      nanoseconds : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| nanoseconds := nanoseconds_value; event_code := event_code_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End SystemEventMessage.

  Module BaseReferenceMessage.

    (** Indicates the base reference number to which all the order, quote and trade reference number deltas must be added to obtain the absolute order or quote Nasdaq reference number. Sent prior to any order, quote and trade messages. *)
    Record t := {
      nanoseconds : N;
      base_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (base_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (base_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (base_reference_number_value, bytes) =>
              Some ({| nanoseconds := nanoseconds_value; base_reference_number := base_reference_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End BaseReferenceMessage.

  Module OptionsDirectoryMessage.

    (** At the start of each trading day, Nasdaq disseminates options symbol directory messages for all active options symbols in the Nasdaq option system. Intra-day updates are sent as they occur; for a given Option Id the canonical information is invariant. *)
    Record t := {
      nanoseconds : N;
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
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
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
      encode_uint 4 (nanoseconds record) ++
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
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
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
                                                          Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; security_symbol := security_symbol_value; expiration_year := expiration_year_value; expiration_month := expiration_month_value; expiration_date := expiration_date_value; explicit_strike_price := explicit_strike_price_value; option_type := option_type_value; source := source_value; underlying_symbol := underlying_symbol_value; options_closing_type := options_closing_type_value; tradable := tradable_value; mpv := mpv_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsDirectoryMessage.

  Module OptionsTradingActionMessage.

    (** Nasdaq uses this administrative message to indicate the current trading status of an index or equity option within the Nasdaq Options Market. Prior to the start of system hours Nasdaq sends a Trading Action spin carrying T (Trading Resumption) for every contract eligible for trading; an option absent from the spin should be treated as halted. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_trading_state_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; current_trading_state := current_trading_state_value |}, bytes)
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

  End OptionsTradingActionMessage.

  Module OptionOpenMessage.

    (** Disseminated for each option as soon as the opening is completed. On the open state the option is available for auto execution within the Nasdaq Options Market System; on the closed state it is no longer eligible. Recipients should continue to process the Trading Action spin, which this message does not override. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      open_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_bytes 1 (open_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (option_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_state_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; open_state := open_state_value |}, bytes)
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

  End OptionOpenMessage.

  Module AddOrderMessageShortForm.

    (** Indicates that a new order has been accepted by the Nasdaq Option system and was added to the displayable book, carrying a day unique Order Reference Number. The short form of the message, published for bandwidth efficiency. *)
    Record t := {
      nanoseconds : N;
      order_reference_number_delta : N;
      market_side : list byte;
      option_id : N;
      price : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_side record) = 1 /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_reference_number_delta record) ++
      encode_bytes 1 (market_side record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 2 (price record) ++
      encode_uint 2 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_reference_number_delta_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_side_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (option_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; order_reference_number_delta := order_reference_number_delta_value; market_side := market_side_value; option_id := option_id_value; price := price_value; volume := volume_value |}, bytes)
                          end
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessageShortForm.

  Module AddOrderMessageLongForm.

    (** Indicates that a new order has been accepted by the Nasdaq Option system and was added to the displayable book, carrying a day unique Order Reference Number. The long form of the message, with four byte price and volume. *)
    Record t := {
      nanoseconds : N;
      order_reference_number_delta : N;
      market_side : list byte;
      option_id : N;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_side record) = 1 /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_reference_number_delta record) ++
      encode_bytes 1 (market_side record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_reference_number_delta_value, bytes) =>
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
                              Some ({| nanoseconds := nanoseconds_value; order_reference_number_delta := order_reference_number_delta_value; market_side := market_side_value; option_id := option_id_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessageLongForm.

  Module AddQuoteMessageShortForm.

    (** Indicates that a new quote has been accepted by the Nasdaq Option system and was added to the displayable book, carrying unique Bid and Ask Reference Numbers. The short form of the message, published for bandwidth efficiency. *)
    Record t := {
      nanoseconds : N;
      bid_reference_number_delta : N;
      ask_reference_number_delta : N;
      option_id : N;
      bid_price : N;
      bid_size : N;
      ask_price : N;
      ask_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (bid_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (ask_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 2)%N /\
      (bid_size record < 256 ^ N.of_nat 2)%N /\
      (ask_price record < 256 ^ N.of_nat 2)%N /\
      (ask_size record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (bid_reference_number_delta record) ++
      encode_uint 4 (ask_reference_number_delta record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 2 (bid_price record) ++
      encode_uint 2 (bid_size record) ++
      encode_uint 2 (ask_price record) ++
      encode_uint 2 (ask_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (bid_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (ask_reference_number_delta_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (option_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (bid_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (bid_size_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ask_size_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; bid_reference_number_delta := bid_reference_number_delta_value; ask_reference_number_delta := ask_reference_number_delta_value; option_id := option_id_value; bid_price := bid_price_value; bid_size := bid_size_value; ask_price := ask_price_value; ask_size := ask_size_value |}, bytes)
                                  end
                              end
                          end
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AddQuoteMessageShortForm.

  Module AddQuoteMessageLongForm.

    (** Indicates that a new quote has been accepted by the Nasdaq Option system and was added to the displayable book, carrying unique Bid and Ask Reference Numbers. The long form of the message, with four byte prices and sizes. *)
    Record t := {
      nanoseconds : N;
      bid_reference_number_delta : N;
      ask_reference_number_delta : N;
      option_id : N;
      bid : N;
      bid_size_long : N;
      ask : N;
      ask_size_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (bid_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (ask_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (bid record < 256 ^ N.of_nat 4)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask record < 256 ^ N.of_nat 4)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (bid_reference_number_delta record) ++
      encode_uint 4 (ask_reference_number_delta record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (bid record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 4 (ask record) ++
      encode_uint 4 (ask_size_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (bid_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (ask_reference_number_delta_value, bytes) =>
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
                                      Some ({| nanoseconds := nanoseconds_value; bid_reference_number_delta := bid_reference_number_delta_value; ask_reference_number_delta := ask_reference_number_delta_value; option_id := option_id_value; bid := bid_value; bid_size_long := bid_size_long_value; ask := ask_value; ask_size_long := ask_size_long_value |}, bytes)
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AddQuoteMessageLongForm.

  Module SingleSideExecutedMessage.

    (** Sent whenever a Side order, an order or one side of a quote, is executed in whole or in part. Several of these messages may be received for the same Side order when it is executed in several parts, and they are cumulative. *)
    Record t := {
      nanoseconds : N;
      reference_number_delta : N;
      executed_contracts : N;
      cross_number : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (executed_contracts record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (reference_number_delta record) ++
      encode_uint 4 (executed_contracts record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_contracts_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cross_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; reference_number_delta := reference_number_delta_value; executed_contracts := executed_contracts_value; cross_number := cross_number_value; match_number := match_number_value |}, bytes)
                      end
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

  End SingleSideExecutedMessage.

  Module SingleSideExecutedWithPriceMessage.

    (** Sent whenever an incoming Side order is executed against the book in whole or in part at a price different from the initial display price, so the execution price is carried in the message. *)
    Record t := {
      nanoseconds : N;
      reference_number_delta : N;
      cross_number : N;
      match_number : N;
      printable : list byte;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (reference_number_delta record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reference_number_delta_value, bytes) =>
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
                                  Some ({| nanoseconds := nanoseconds_value; reference_number_delta := reference_number_delta_value; cross_number := cross_number_value; match_number := match_number_value; printable := printable_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideExecutedWithPriceMessage.

  Module OrderCancelMessage.

    (** Sent whenever an order on the book is modified as a result of a partial cancellation. *)
    Record t := {
      nanoseconds : N;
      order_reference_number_delta : N;
      cancelled_contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (cancelled_contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_reference_number_delta record) ++
      encode_uint 4 (cancelled_contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cancelled_contracts_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; order_reference_number_delta := order_reference_number_delta_value; cancelled_contracts := cancelled_contracts_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End OrderCancelMessage.

  Module SingleSideReplaceMessageShortForm.

    (** Sent whenever an order or one side of a quote on the book is replaced. The replacement has a new sequence number and replaces the prior sequence number. The short form of the message, published for bandwidth efficiency. *)
    Record t := {
      nanoseconds : N;
      original_reference_number_delta : N;
      new_reference_number_delta : N;
      price : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (original_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (new_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (original_reference_number_delta record) ++
      encode_uint 4 (new_reference_number_delta record) ++
      encode_uint 2 (price record) ++
      encode_uint 2 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (original_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (new_reference_number_delta_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; original_reference_number_delta := original_reference_number_delta_value; new_reference_number_delta := new_reference_number_delta_value; price := price_value; volume := volume_value |}, bytes)
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

  End SingleSideReplaceMessageShortForm.

  Module SingleSideReplaceMessageLongForm.

    (** Sent whenever an order or one side of a quote on the book is replaced. The replacement has a new sequence number and replaces the prior sequence number. The long form of the message, with four byte price and volume. *)
    Record t := {
      nanoseconds : N;
      original_reference_number_delta : N;
      new_reference_number_delta : N;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (original_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (new_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (original_reference_number_delta record) ++
      encode_uint 4 (new_reference_number_delta record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (original_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (new_reference_number_delta_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volume_long_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; original_reference_number_delta := original_reference_number_delta_value; new_reference_number_delta := new_reference_number_delta_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                      end
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

  End SingleSideReplaceMessageLongForm.

  Module SingleSideDeleteMessage.

    (** Sent when an order or a side of a quote is being cancelled. All remaining contracts are no longer accessible so the side should be removed from the book. *)
    Record t := {
      nanoseconds : N;
      reference_number_delta : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (reference_number_delta record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (reference_number_delta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reference_number_delta_value, bytes) =>
              Some ({| nanoseconds := nanoseconds_value; reference_number_delta := reference_number_delta_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SingleSideDeleteMessage.

  Module SingleSideUpdateMessage.

    (** Sent whenever an order or a side of a quote is being updated for price and or contracts. The reference number associated with the order or quote is unchanged and it retains its priority on the book. *)
    Record t := {
      nanoseconds : N;
      reference_number_delta : N;
      change_reason : list byte;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (change_reason record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (reference_number_delta record) ++
      encode_bytes 1 (change_reason record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (reference_number_delta_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (change_reason_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volume_long_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; reference_number_delta := reference_number_delta_value; change_reason := change_reason_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideUpdateMessage.

  Module QuoteReplaceMessageShortForm.

    (** Sent whenever a quote on the book is replaced. The replaced quote has new sequence numbers on both sides, replacing the prior sequence numbers. The short form of the message, published for bandwidth efficiency. *)
    Record t := {
      nanoseconds : N;
      original_bid_reference_number_delta : N;
      bid_reference_number_delta : N;
      original_ask_reference_number_delta : N;
      ask_reference_delta_number : N;
      bid_price : N;
      bid_size : N;
      ask_price : N;
      ask_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (original_bid_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (bid_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (original_ask_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (ask_reference_delta_number record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 2)%N /\
      (bid_size record < 256 ^ N.of_nat 2)%N /\
      (ask_price record < 256 ^ N.of_nat 2)%N /\
      (ask_size record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (original_bid_reference_number_delta record) ++
      encode_uint 4 (bid_reference_number_delta record) ++
      encode_uint 4 (original_ask_reference_number_delta record) ++
      encode_uint 4 (ask_reference_delta_number record) ++
      encode_uint 2 (bid_price record) ++
      encode_uint 2 (bid_size record) ++
      encode_uint 2 (ask_price record) ++
      encode_uint 2 (ask_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (original_bid_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_reference_number_delta_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_ask_reference_number_delta_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_reference_delta_number_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (bid_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (bid_size_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ask_price_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_size_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; original_bid_reference_number_delta := original_bid_reference_number_delta_value; bid_reference_number_delta := bid_reference_number_delta_value; original_ask_reference_number_delta := original_ask_reference_number_delta_value; ask_reference_delta_number := ask_reference_delta_number_value; bid_price := bid_price_value; bid_size := bid_size_value; ask_price := ask_price_value; ask_size := ask_size_value |}, bytes)
                                      end
                                  end
                              end
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

  End QuoteReplaceMessageShortForm.

  Module QuoteReplaceMessageLongForm.

    (** Sent whenever a quote on the book is replaced. The replaced quote has new sequence numbers on both sides, replacing the prior sequence numbers. The long form of the message, with four byte prices and sizes. *)
    Record t := {
      nanoseconds : N;
      original_bid_reference_number_delta : N;
      bid_reference_number_delta : N;
      original_ask_reference_number_delta : N;
      ask_reference_delta_number : N;
      bid_price_long : N;
      bid_size_long : N;
      ask_price_long : N;
      ask_size_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (original_bid_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (bid_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (original_ask_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (ask_reference_delta_number record < 256 ^ N.of_nat 4)%N /\
      (bid_price_long record < 256 ^ N.of_nat 4)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask_price_long record < 256 ^ N.of_nat 4)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (original_bid_reference_number_delta record) ++
      encode_uint 4 (bid_reference_number_delta record) ++
      encode_uint 4 (original_ask_reference_number_delta record) ++
      encode_uint 4 (ask_reference_delta_number record) ++
      encode_uint 4 (bid_price_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 4 (ask_price_long record) ++
      encode_uint 4 (ask_size_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (original_bid_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_reference_number_delta_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_ask_reference_number_delta_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_reference_delta_number_value, bytes) =>
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
                                          Some ({| nanoseconds := nanoseconds_value; original_bid_reference_number_delta := original_bid_reference_number_delta_value; bid_reference_number_delta := bid_reference_number_delta_value; original_ask_reference_number_delta := original_ask_reference_number_delta_value; ask_reference_delta_number := ask_reference_delta_number_value; bid_price_long := bid_price_long_value; bid_size_long := bid_size_long_value; ask_price_long := ask_price_long_value; ask_size_long := ask_size_long_value |}, bytes)
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

  End QuoteReplaceMessageLongForm.

  Module QuoteDeleteMessage.

    (** Sent when a single quote is being cancelled. All remaining contracts are no longer accessible so the quote should be removed from the book. *)
    Record t := {
      nanoseconds : N;
      bid_reference_number_delta : N;
      ask_reference_number_delta : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (bid_reference_number_delta record < 256 ^ N.of_nat 4)%N /\
      (ask_reference_number_delta record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (bid_reference_number_delta record) ++
      encode_uint 4 (ask_reference_number_delta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (bid_reference_number_delta_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (ask_reference_number_delta_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; bid_reference_number_delta := bid_reference_number_delta_value; ask_reference_number_delta := ask_reference_number_delta_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End QuoteDeleteMessage.

  Module OptionsTradeNonAuctionMessage.

    (** Provides execution details for normal match events involving non displayable order types, for which no Add Order or Add Quote message is generated. Auction events are reported separately by the Options Cross Trade message. *)
    Record t := {
      nanoseconds : N;
      buy_sell_indicator : list byte;
      option_id : N;
      cross_number : N;
      match_number : N;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
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
                                  Some ({| nanoseconds := nanoseconds_value; buy_sell_indicator := buy_sell_indicator_value; option_id := option_id_value; cross_number := cross_number_value; match_number := match_number_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsTradeNonAuctionMessage.

  Module OptionsCrossTradeMessage.

    (** Sent for every option when an auction in that option is completed, indicating the bulk volume associated with the auction event. Also used to report all executions within a price improvement (PRISM) auction. To avoid double counting of auction volume, firms should not include transactions marked as auction trades. *)
    Record t := {
      nanoseconds : N;
      option_id : N;
      cross_number : N;
      match_number : N;
      cross_type : list byte;
      price_long : N;
      volume_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (option_id record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (option_id record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
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
                                  Some ({| nanoseconds := nanoseconds_value; option_id := option_id_value; cross_number := cross_number_value; match_number := match_number_value; cross_type := cross_type_value; price_long := price_long_value; volume_long := volume_long_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsCrossTradeMessage.

  Module BrokenTradeOrOrderExecutionMessage.

    (** Sent whenever an execution on Nasdaq is broken, which may happen if it is found to be clearly erroneous pursuant to the Nasdaq Clearly Erroneous Policy. A trade break is final; once a trade is broken it cannot be reinstated. *)
    Record t := {
      nanoseconds : N;
      cross_number : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (cross_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (match_number_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; cross_number := cross_number_value; match_number := match_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End BrokenTradeOrOrderExecutionMessage.

  Module NetOrderImbalanceIndicatorMessage.

    (** Nasdaq disseminates Net Order Imbalance Indicator data at five second intervals in the minutes leading up to the Nasdaq Opening Auction events, and for price improvement (PRISM) auctions. *)
    Record t := {
      nanoseconds : N;
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
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
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
      encode_uint 4 (nanoseconds record) ++
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
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
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
                                              Some ({| nanoseconds := nanoseconds_value; auction_id := auction_id_value; auction_type := auction_type_value; paired_contracts := paired_contracts_value; imbalance_direction := imbalance_direction_value; option_id := option_id_value; imbalance_price := imbalance_price_value; imbalance_volume := imbalance_volume_value; customer_firm_indicator := customer_firm_indicator_value; reserved_3 := reserved_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetOrderImbalanceIndicatorMessage.

End NomOptionsIttoV32Server.
