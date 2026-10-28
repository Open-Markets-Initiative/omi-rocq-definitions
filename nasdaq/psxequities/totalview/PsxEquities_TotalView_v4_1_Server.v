From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch

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

Module PsxEquitiesTotalViewV41Server.

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

  Module TimestampSecondsMessage.

    (** Reflects the number of seconds past midnight that the Timestamp message was generated. A Timestamp - Second message will be disseminated for every second for which there is at least one payload message. *)
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

  End TimestampSecondsMessage.

  Module SystemEventMessage.

    (** PSX GLIMPSE product is designed to support the same system event messages as the PSX TotalView-ITCH feed. On PSX GLIMPSE, PSX will send out system event messages for those events that occurred up to the time of the PSX GLIMPSE snapshot request. *)
    Record t := {
      timestamp_nanoseconds : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; event_code := event_code_value |}, bytes)
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

  Module AddOrderMessage.

    (** Add Order - No MPID Attribution Message. This message will be generated for unattributed orders accepted by the PSX system. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      shares : N;
      stock : list byte;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_reference_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (buy_sell_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (shares_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (stock_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module AddOrderMpidAttributionMessage.

    (** Add Order with MPID Attribution Message. This message will be generated for attributed orders and quotations accepted by the PSX system. Note: This message will not be supported for NASDAQ OMX PSX for initial market launch. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      shares : N;
      stock : list byte;
      price : N;
      attribution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (attribution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (price record) ++
      encode_bytes 4 (attribution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_reference_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (buy_sell_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (shares_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (stock_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (attribution_value, bytes) =>
                                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; attribution := attribution_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMpidAttributionMessage.

  Module StockDirectoryMessage.

    (** At the start of each trading day, NASDAQ OMX PSX disseminates stock directory messages for all active symbols in the system for the current trading day. Please note that the Symbol Directory spin may include halted issues. *)
    Record t := {
      timestamp_nanoseconds : N;
      stock : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
      round_lot_size : N;
      round_lots_only : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (round_lots_only record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_bytes 1 (round_lots_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (stock_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_category_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (financial_status_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (round_lot_size_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (round_lots_only_value, bytes) =>
                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; stock := stock_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End StockDirectoryMessage.

  Module StockTradingActionMessage.

    (** In the GLIMPSE transmission, PSX will send out a Stock Trading Action message for only those NASDAQ, NYSE, NYSE Amex, NYSE Arca and BATS issues that were eligible for trading during the current trading session. *)
    Record t := {
      timestamp_nanoseconds : N;
      stock : list byte;
      trading_state : list byte;
      reserved : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (reserved record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (stock_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_state_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (reason_value, bytes) =>
                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; stock := stock_value; trading_state := trading_state_value; reserved := reserved_value; reason := reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End StockTradingActionMessage.

  Module RegShoRestrictionMessage.

    (** Reg SHO Short Sale Price Test Restricted Indicator *)
    Record t := {
      timestamp_nanoseconds : N;
      stock : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (stock_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reg_sho_action_value, bytes) =>
                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; stock := stock_value; reg_sho_action := reg_sho_action_value |}, bytes)
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

  End RegShoRestrictionMessage.

  Module EndOfSnapshotMessage.

    (** The Snapshot message reflects the PSX TotalView-ITCH 4.1 sequence number at the time that the PSX GLIMPSE 4.1 spin was requested. *)
    Record t := {
      itch_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (itch_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (itch_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (itch_sequence_number_value, bytes) =>
          Some ({| itch_sequence_number := itch_sequence_number_value |}, bytes)
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

  End EndOfSnapshotMessage.

End PsxEquitiesTotalViewV41Server.
