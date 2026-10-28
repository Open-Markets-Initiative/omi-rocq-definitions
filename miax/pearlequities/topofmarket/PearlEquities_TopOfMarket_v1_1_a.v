From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Top Of Market

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
      - a field of no fixed width
  *)

Module PearlEquitiesTopOfMarketV11A.

  Module MachPacketHeader.

    (** Mach packet header (12 bytes) *)
    Record t := {
      sequence_number : N;
      mach_packet_length : N;
      mach_packet_type : N;
      session_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (mach_packet_length record < 256 ^ N.of_nat 2)%N /\
      (mach_packet_type record < 256 ^ N.of_nat 1)%N /\
      (session_number record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (mach_packet_length record) ++
      encode_uint 1 (mach_packet_type record) ++
      encode_uint 1 (session_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (mach_packet_length_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (mach_packet_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_number_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; mach_packet_length := mach_packet_length_value; mach_packet_type := mach_packet_type_value; session_number := session_number_value |}, bytes)
                  end
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

  End MachPacketHeader.

  Module SystemTimeMessage.

    (** This is the message format that will be used to disseminate the “seconds” part of the timestamp that is applicable to all messages that are sent in the current second. *)
    Record t := {
      seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          Some ({| seconds := seconds_value |}, bytes)
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

  End SystemTimeMessage.

  Module SymbolUpdateMessage.

    (** This is the message format that will be used to disseminate all security symbols traded on MIAX PEARL Equities for the current trading session. The Symbol ID sent in this message will be disseminated in Top of Market and Last Sale messages. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
      ticker_symbol : list byte;
      reserved_1 : N;
      test_security_indicator : list byte;
      second_reserved_1 : N;
      lot_size : N;
      opening_time : list byte;
      closing_time : list byte;
      primary_market_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ticker_symbol record) = 11 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (test_security_indicator record) = 1 /\
      (second_reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (lot_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (opening_time record) = 8 /\
      Datatypes.length (closing_time record) = 8 /\
      Datatypes.length (primary_market_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record) ++
      encode_bytes 11 (ticker_symbol record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (test_security_indicator record) ++
      encode_uint 1 (second_reserved_1 record) ++
      encode_uint 2 (lot_size record) ++
      encode_bytes 8 (opening_time record) ++
      encode_bytes 8 (closing_time record) ++
      encode_bytes 1 (primary_market_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
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
                              match decode_uint 2 bytes with
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
                                              Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; ticker_symbol := ticker_symbol_value; reserved_1 := reserved_1_value; test_security_indicator := test_security_indicator_value; second_reserved_1 := second_reserved_1_value; lot_size := lot_size_value; opening_time := opening_time_value; closing_time := closing_time_value; primary_market_code := primary_market_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolUpdateMessage.

  Module SystemStateMessage.

    (** This is the message format that will be used to notify firms of the state changes of the system. This is a notification that applies to all symbols on the feed. Firms can use notifications as triggers in their system to ensure electronic synchronization of systems. *)
    Record t := {
      nanoseconds : N;
      to_m_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (to_m_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (to_m_version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (to_m_version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; to_m_version := to_m_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemStateMessage.

  Module SecurityTradingStatusNotificationMessage.

    (** This is the message format that will be used to notify firms of changes to the trading status of a particular security. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
      trading_status : N;
      market_state : N;
      short_sale_restriction : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (trading_status record < 256 ^ N.of_nat 1)%N /\
      (market_state record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (short_sale_restriction record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 1 (trading_status record) ++
      encode_uint 1 (market_state record) ++
      encode_bytes 1 (short_sale_restriction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_state_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (short_sale_restriction_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; trading_status := trading_status_value; market_state := market_state_value; short_sale_restriction := short_sale_restriction_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityTradingStatusNotificationMessage.

  Module CompactTopOfMarketBestBidAndOfferMessage.

    (** This is the message format that will be used to publish MIAX PEARL Best Bid and Offer (MPBBO) of a security with MPBBO values that can fit in this compact format. In the compact format both bid and offer prices have 2 decimal places and are limited to a maximum value of $655.35. Bid and Offer sizes are limited to 65,535 shares. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
      bid_price : N;
      bid_size : N;
      offer_price : N;
      offer_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 2)%N /\
      (bid_size record < 256 ^ N.of_nat 2)%N /\
      (offer_price record < 256 ^ N.of_nat 2)%N /\
      (offer_size record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 2 (bid_price record) ++
      encode_uint 2 (bid_size record) ++
      encode_uint 2 (offer_price record) ++
      encode_uint 2 (offer_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (bid_price_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_size_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (offer_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (offer_size_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; bid_price := bid_price_value; bid_size := bid_size_value; offer_price := offer_price_value; offer_size := offer_size_value |}, bytes)
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

  End CompactTopOfMarketBestBidAndOfferMessage.

  Module WideTopOfMarketBestBidAndOfferMessage.

    (** This is the message format that will be used to publish MIAX PEARL Best Bid and Offer (MPBBO) of a security with MPBBO values that will not fit in the compact format. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
      bid_price : N;
      bid_size : N;
      offer_price : N;
      offer_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 2)%N /\
      (bid_size record < 256 ^ N.of_nat 2)%N /\
      (offer_price record < 256 ^ N.of_nat 2)%N /\
      (offer_size record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 2 (bid_price record) ++
      encode_uint 2 (bid_size record) ++
      encode_uint 2 (offer_price record) ++
      encode_uint 2 (offer_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (bid_price_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_size_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (offer_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (offer_size_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; bid_price := bid_price_value; bid_size := bid_size_value; offer_price := offer_price_value; offer_size := offer_size_value |}, bytes)
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

  End WideTopOfMarketBestBidAndOfferMessage.

  Module TradeCancelMessage.

    (** This is the message format that will be used to disseminate canceled trades that are resulting from Trade cancellations on MIAX PEARL Equities during the current trading session. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
      trade_id : N;
      correction_number : N;
      price : N;
      size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (correction_number record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 1 (correction_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (correction_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (size_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; trade_id := trade_id_value; correction_number := correction_number_value; price := price_value; size := size_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End TradeCancelMessage.

End PearlEquitiesTopOfMarketV11A.
