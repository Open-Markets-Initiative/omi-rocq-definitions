From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group Genium Inet

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

Module OseDerivativesGeniumInetV22Server.

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

    (** Provides data on the seconds when each message is disseminated. *)
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

  Module SeriesInformationBasicMessage.

    (** Provides detailed data about the series that can be traded on a given business day. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      symbol : list byte;
      long_name : list byte;
      reserved_12 : list byte;
      financial_product : N;
      trading_currency : list byte;
      number_of_decimals_in_price : N;
      number_of_decimals_in_nominal_value : N;
      odd_lot_size : N;
      round_lot_size : N;
      block_lot_size : N;
      nominal_value : N;
      number_of_legs : N;
      underlying_order_book_id : N;
      strike_price : N;
      expiration_date : N;
      number_of_decimals_in_strike_price : N;
      put_or_call : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 32 /\
      Datatypes.length (long_name record) = 32 /\
      Datatypes.length (reserved_12 record) = 12 /\
      (financial_product record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_currency record) = 3 /\
      (number_of_decimals_in_price record < 256 ^ N.of_nat 2)%N /\
      (number_of_decimals_in_nominal_value record < 256 ^ N.of_nat 2)%N /\
      (odd_lot_size record < 256 ^ N.of_nat 4)%N /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (nominal_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_legs record < 256 ^ N.of_nat 1)%N /\
      (underlying_order_book_id record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (number_of_decimals_in_strike_price record < 256 ^ N.of_nat 2)%N /\
      (put_or_call record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_bytes 32 (long_name record) ++
      encode_bytes 12 (reserved_12 record) ++
      encode_uint 1 (financial_product record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_uint 2 (number_of_decimals_in_price record) ++
      encode_uint 2 (number_of_decimals_in_nominal_value record) ++
      encode_uint 4 (odd_lot_size record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_uint 4 (block_lot_size record) ++
      encode_uint 8 (nominal_value record) ++
      encode_uint 1 (number_of_legs record) ++
      encode_uint 4 (underlying_order_book_id record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (expiration_date record) ++
      encode_uint 2 (number_of_decimals_in_strike_price record) ++
      encode_uint 1 (put_or_call record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (long_name_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (reserved_12_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (financial_product_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (trading_currency_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (number_of_decimals_in_price_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (number_of_decimals_in_nominal_value_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (odd_lot_size_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (round_lot_size_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (block_lot_size_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (nominal_value_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (number_of_legs_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (underlying_order_book_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (strike_price_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (expiration_date_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (number_of_decimals_in_strike_price_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (put_or_call_value, bytes) =>
                                                                                  Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; symbol := symbol_value; long_name := long_name_value; reserved_12 := reserved_12_value; financial_product := financial_product_value; trading_currency := trading_currency_value; number_of_decimals_in_price := number_of_decimals_in_price_value; number_of_decimals_in_nominal_value := number_of_decimals_in_nominal_value_value; odd_lot_size := odd_lot_size_value; round_lot_size := round_lot_size_value; block_lot_size := block_lot_size_value; nominal_value := nominal_value_value; number_of_legs := number_of_legs_value; underlying_order_book_id := underlying_order_book_id_value; strike_price := strike_price_value; expiration_date := expiration_date_value; number_of_decimals_in_strike_price := number_of_decimals_in_strike_price_value; put_or_call := put_or_call_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 128.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesInformationBasicMessage.

  Module SeriesInformationBasicCombinationMessage.

    (** Provides detailed data about the legs of combination trading instruments that can be traded on a given trading day. *)
    Record t := {
      nanoseconds : N;
      combination_order_book_id : N;
      leg_order_book_id : N;
      leg_side : list byte;
      leg_ratio : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (combination_order_book_id record < 256 ^ N.of_nat 4)%N /\
      (leg_order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side record) = 1 /\
      (leg_ratio record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (combination_order_book_id record) ++
      encode_uint 4 (leg_order_book_id record) ++
      encode_bytes 1 (leg_side record) ++
      encode_uint 4 (leg_ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (combination_order_book_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (leg_order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (leg_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (leg_ratio_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; combination_order_book_id := combination_order_book_id_value; leg_order_book_id := leg_order_book_id_value; leg_side := leg_side_value; leg_ratio := leg_ratio_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesInformationBasicCombinationMessage.

  Module TickSizeDataMessage.

    (** Provides the tick size of a trading instrument. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      tick_size : N;
      price_from : N;
      price_to : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (price_from record < 256 ^ N.of_nat 4)%N /\
      (price_to record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 4 (price_from record) ++
      encode_uint 4 (price_to record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tick_size_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_from_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_to_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; tick_size := tick_size_value; price_from := price_from_value; price_to := price_to_value |}, bytes)
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

  End TickSizeDataMessage.

  Module SystemEventDataMessage.

    (** Provides system event update data. *)
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

  End SystemEventDataMessage.

  Module TradingStatusDataMessage.

    (** Provides the trading status data of a trading instrument. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      state_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (state_name record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 20 (state_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (state_name_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; state_name := state_name_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusDataMessage.

  Module NewOrderMessage.

    (** Provides quote data related to a new order. *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
      order_book_position : N;
      quantity : N;
      price : N;
      order_attributes : N;
      lot_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_book_position record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (order_attributes record < 256 ^ N.of_nat 2)%N /\
      (lot_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (order_book_position record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 2 (order_attributes record) ++
      encode_uint 1 (lot_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_book_position_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (order_attributes_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (lot_type_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value; order_book_position := order_book_position_value; quantity := quantity_value; price := price_value; order_attributes := order_attributes_value; lot_type := lot_type_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderMessage.

  Module ExecutionNoticeMessage.

    (** Provides an execution notice. The Order ID of the order which is already in the order book is set. *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
      executed_quantity : N;
      match_id : N;
      combo_group_id : N;
      reserved_7_a : N;
      reserved_7_b : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_7_a record < 256 ^ N.of_nat 7)%N /\
      (reserved_7_b record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_uint 7 (reserved_7_a record) ++
      encode_uint 7 (reserved_7_b record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (executed_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (combo_group_id_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (reserved_7_a_value, bytes) =>
                                      match decode_uint 7 bytes with
                                      | None => None
                                      | Some (reserved_7_b_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value; executed_quantity := executed_quantity_value; match_id := match_id_value; combo_group_id := combo_group_id_value; reserved_7_a := reserved_7_a_value; reserved_7_b := reserved_7_b_value |}, bytes)
                                      end
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionNoticeMessage.

  Module ExecutionNoticeWithTradeInformationMessage.

    (** Provides an execution notice with trade information. *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
      executed_quantity : N;
      match_id : N;
      combo_group_id : N;
      reserved_7_a : N;
      reserved_7_b : N;
      trade_price : N;
      occurred_at_cross : list byte;
      printable : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_7_a record < 256 ^ N.of_nat 7)%N /\
      (reserved_7_b record < 256 ^ N.of_nat 7)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (occurred_at_cross record) = 1 /\
      Datatypes.length (printable record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_uint 7 (reserved_7_a record) ++
      encode_uint 7 (reserved_7_b record) ++
      encode_uint 4 (trade_price record) ++
      encode_bytes 1 (occurred_at_cross record) ++
      encode_bytes 1 (printable record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (executed_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (combo_group_id_value, bytes) =>
                                  match decode_uint 7 bytes with
                                  | None => None
                                  | Some (reserved_7_a_value, bytes) =>
                                      match decode_uint 7 bytes with
                                      | None => None
                                      | Some (reserved_7_b_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (occurred_at_cross_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (printable_value, bytes) =>
                                                      Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value; executed_quantity := executed_quantity_value; match_id := match_id_value; combo_group_id := combo_group_id_value; reserved_7_a := reserved_7_a_value; reserved_7_b := reserved_7_b_value; trade_price := trade_price_value; occurred_at_cross := occurred_at_cross_value; printable := printable_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionNoticeWithTradeInformationMessage.

  Module DeletedOrderMessage.

    (** Provided when an order is deleted and does not exist in the order book. *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value |}, bytes)
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

  End DeletedOrderMessage.

  Module EpMessage.

    (** Provides the equilibrium price for the order reception hours. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      available_bid_quantity_at_equilibrium_price : N;
      available_ask_quantity_at_equilibrium_price : N;
      equilibrium_price : N;
      reserved_4_a : N;
      reserved_4_b : N;
      reserved_8_a : N;
      reserved_8_b : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (available_bid_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (available_ask_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 4)%N /\
      (reserved_4_a record < 256 ^ N.of_nat 4)%N /\
      (reserved_4_b record < 256 ^ N.of_nat 4)%N /\
      (reserved_8_a record < 256 ^ N.of_nat 8)%N /\
      (reserved_8_b record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (available_bid_quantity_at_equilibrium_price record) ++
      encode_uint 8 (available_ask_quantity_at_equilibrium_price record) ++
      encode_uint 4 (equilibrium_price record) ++
      encode_uint 4 (reserved_4_a record) ++
      encode_uint 4 (reserved_4_b record) ++
      encode_uint 8 (reserved_8_a record) ++
      encode_uint 8 (reserved_8_b record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (available_bid_quantity_at_equilibrium_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (available_ask_quantity_at_equilibrium_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (equilibrium_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (reserved_4_a_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (reserved_4_b_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (reserved_8_a_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (reserved_8_b_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; available_bid_quantity_at_equilibrium_price := available_bid_quantity_at_equilibrium_price_value; available_ask_quantity_at_equilibrium_price := available_ask_quantity_at_equilibrium_price_value; equilibrium_price := equilibrium_price_value; reserved_4_a := reserved_4_a_value; reserved_4_b := reserved_4_b_value; reserved_8_a := reserved_8_a_value; reserved_8_b := reserved_8_b_value |}, bytes)
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

  End EpMessage.

  Module SnapshotCompletionMessage.

    (** Sent after completing the transmission of snapshot data. *)
    Record t := {
      sequence : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sequence record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End SnapshotCompletionMessage.

End OseDerivativesGeniumInetV22Server.
