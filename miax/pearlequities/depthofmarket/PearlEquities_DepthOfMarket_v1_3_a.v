From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Depth Of Market

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
      - a field read in bits
  *)

Module PearlEquitiesDepthOfMarketV13A.

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

    (** This message is used to disseminate the “seconds” part of the timestamp that is applicable to all messages that are sent in the current second. *)
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
      spare : N;
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
      (spare record < 256 ^ N.of_nat 1)%N /\
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
      encode_uint 1 (spare record) ++
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
                          | Some (spare_value, bytes) =>
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
                                              Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; ticker_symbol := ticker_symbol_value; reserved_1 := reserved_1_value; test_security_indicator := test_security_indicator_value; spare := spare_value; lot_size := lot_size_value; opening_time := opening_time_value; closing_time := closing_time_value; primary_market_code := primary_market_code_value |}, bytes)
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
      do_m_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (do_m_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (do_m_version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (do_m_version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; do_m_version := do_m_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
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

    (** This message is used to notify firms of changes to the trading status of a particular security. *)
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

  Module SymbolClearMessage.

    (** This message format is used to indicate that the MIAX PEARL Equities book for a symbol has been cleared of all orders. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value |}, bytes)
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

  End SymbolClearMessage.

  Module AddOrderMessage.

    (** This is the message format that will be used when a displayed order is received and added to MIAX PEARL Equities book. It includes an Order ID that is unique to the order across the exchange and across trading days. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
      order_id : N;
      order_side : list byte;
      price : N;
      size : N;
      attributable_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (attributable_id record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (order_side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record) ++
      encode_bytes 4 (attributable_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (order_side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (size_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (attributable_id_value, bytes) =>
                                  Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; order_id := order_id_value; order_side := order_side_value; price := price_value; size := size_value; attributable_id := attributable_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module DeleteOrderMessage.

    (** This message format is used to indicate that a displayed order has been removed from the MIAX PEARL Equities book. *)
    Record t := {
      nanoseconds : N;
      symbol_id : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (symbol_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (symbol_id record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; symbol_id := symbol_id_value; order_id := order_id_value |}, bytes)
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

  End DeleteOrderMessage.

  Module TradeCancelMessage.

    (** This message format is used to publish cancellation of a trade which was previously published via an Order Execution Message or a Trade Message. *)
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

End PearlEquitiesDepthOfMarketV13A.
