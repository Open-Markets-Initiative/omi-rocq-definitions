From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Specialized Quote Interface

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

Module NtxOptionsQuotingV90Client.

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
      heartbeat_timeout : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 20 /\
      Datatypes.length (heartbeat_timeout record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 20 (requested_sequence_number record) ++
      encode_bytes 5 (heartbeat_timeout record).

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
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (heartbeat_timeout_value, bytes) =>
                          Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value; heartbeat_timeout := heartbeat_timeout_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequestPacket.

  Module NotificationSubscriptionRequestMessage.

    (** Modifies the set of optional notification types delivered on the current session. *)
    Record t := {
      badge : list byte;
      message_id : N;
      subscription : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (subscription record) = 24.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 24 (subscription record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 24 bytes with
              | None => None
              | Some (subscription_value, bytes) =>
                  Some ({| badge := badge_value; message_id := message_id_value; subscription := subscription_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotificationSubscriptionRequestMessage.

  Module MmParameterDefinitionRequestMessage.

    (** Sets the Rapid Fire/Curtailment parameters (CumQty, Percentage, Delta, Vega and Interval) per underlying and instrument type. Rejected if the badge is configured for ActiveQP. *)
    Record t := {
      badge : list byte;
      message_id : N;
      instrument_type : list byte;
      underlying : list byte;
      interval : N;
      percentage : N;
      cum_qty : N;
      delta : N;
      vega : N;
      reserved_32 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (underlying record) = 13 /\
      (interval record < 256 ^ N.of_nat 2)%N /\
      (percentage record < 256 ^ N.of_nat 2)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (delta record < 256 ^ N.of_nat 4)%N /\
      (vega record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_32 record) = 32.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 13 (underlying record) ++
      encode_uint 2 (interval record) ++
      encode_uint 2 (percentage record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 4 (delta record) ++
      encode_uint 4 (vega record) ++
      encode_bytes 32 (reserved_32 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (instrument_type_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (underlying_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (interval_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (percentage_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (cum_qty_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (delta_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (vega_value, bytes) =>
                                          match decode_bytes 32 bytes with
                                          | None => None
                                          | Some (reserved_32_value, bytes) =>
                                              Some ({| badge := badge_value; message_id := message_id_value; instrument_type := instrument_type_value; underlying := underlying_value; interval := interval_value; percentage := percentage_value; cum_qty := cum_qty_value; delta := delta_value; vega := vega_value; reserved_32 := reserved_32_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MmParameterDefinitionRequestMessage.

  Module ActiveQpSelfReplenishmentSetLimitMessage.

    (** ActiveQP/Self-Replenishment Set Limit Message: sets the contract limit for self-replenishment purge. *)
    Record t := {
      badge : list byte;
      message_id : N;
      underlying_symbol : list byte;
      set_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      (set_value record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_uint 4 (set_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (set_value_value, bytes) =>
                      Some ({| badge := badge_value; message_id := message_id_value; underlying_symbol := underlying_symbol_value; set_value := set_value_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveQpSelfReplenishmentSetLimitMessage.

  Module RapidFireConfigRequestMessage.

    (** Rapid Fire/Curtailment Config Request. Supported on Phlx, NOM and NTX; replaced by the MM Parameter Definition messages. *)
    Record t := {
      badge : list byte;
      underlying_symbol : list byte;
      percentage : N;
      interval : N;
      cum_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (underlying_symbol record) = 13 /\
      (percentage record < 256 ^ N.of_nat 2)%N /\
      (interval record < 256 ^ N.of_nat 2)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_uint 2 (percentage record) ++
      encode_uint 2 (interval record) ++
      encode_uint 4 (cum_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_bytes 13 bytes with
          | None => None
          | Some (underlying_symbol_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (percentage_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (interval_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (cum_qty_value, bytes) =>
                          Some ({| badge := badge_value; underlying_symbol := underlying_symbol_value; percentage := percentage_value; interval := interval_value; cum_qty := cum_qty_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RapidFireConfigRequestMessage.

  Module UnderlyingPurgeRequestMessage.

    (** Underlying Purge Message including SentTimestamp: pulls all quotes for all options contracts of the specified underlying and inhibits new quotes until reentry. *)
    Record t := {
      badge : list byte;
      message_id : N;
      sent_timestamp : N;
      underlying_symbol : list byte;
      instrument_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (sent_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (instrument_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 8 (sent_timestamp record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (instrument_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sent_timestamp_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (underlying_symbol_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (instrument_type_value, bytes) =>
                          Some ({| badge := badge_value; message_id := message_id_value; sent_timestamp := sent_timestamp_value; underlying_symbol := underlying_symbol_value; instrument_type := instrument_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingPurgeRequestMessage.

  Module MarketReentryRequestMessage.

    (** Market Reentry Message: resets risk protection previously triggered by a Rapid Fire/Curtailment event or a user Purge request. *)
    Record t := {
      badge : list byte;
      message_id : N;
      underlying_symbol : list byte;
      instrument_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (instrument_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (instrument_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (instrument_type_value, bytes) =>
                      Some ({| badge := badge_value; message_id := message_id_value; underlying_symbol := underlying_symbol_value; instrument_type := instrument_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketReentryRequestMessage.

  Module ActiveQpSelfReplenishmentRequestReentryMessage.

    (** ActiveQP/Self-Replenishment Request/Reentry Message: partial replenishment (removes a number of contracts from the Active QP counter) or full replenishment/reentry (value 0). *)
    Record t := {
      badge : list byte;
      message_id : N;
      underlying_symbol : list byte;
      replenishment_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      (replenishment_value record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_uint 4 (replenishment_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (replenishment_value_value, bytes) =>
                      Some ({| badge := badge_value; message_id := message_id_value; underlying_symbol := underlying_symbol_value; replenishment_value := replenishment_value_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveQpSelfReplenishmentRequestReentryMessage.

  Module SimpleMsarRequestMessage.

    (** SQF Market Sweep and Auction Response (MSAR) request for a simple instrument. A size of zero cancels a prior auction response for the same instrument/price/side. *)
    Record t := {
      badge : list byte;
      message_id : N;
      instrument_id : N;
      msar_type : list byte;
      auction_id : N;
      price : N;
      side : list byte;
      contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (msar_type record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (msar_type record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (msar_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (auction_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (contracts_value, bytes) =>
                                      Some ({| badge := badge_value; message_id := message_id_value; instrument_id := instrument_id_value; msar_type := msar_type_value; auction_id := auction_id_value; price := price_value; side := side_value; contracts := contracts_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleMsarRequestMessage.

  Module ComplexMsarRequestMessage.

    (** MSAR request for a complex instrument. Price cannot be negative; the Debit/Credit indicator gives the sign. *)
    Record t := {
      badge : list byte;
      message_id : N;
      instrument_id : N;
      msar_type : list byte;
      auction_id : N;
      price : N;
      side : list byte;
      debit_credit : list byte;
      contracts : N;
      price_protection : list byte;
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (msar_type record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (debit_credit record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_protection record) = 1 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (msar_type record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (debit_credit record) ++
      encode_uint 4 (contracts record) ++
      encode_bytes 1 (price_protection record) ++
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (msar_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (auction_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (debit_credit_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (contracts_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (price_protection_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (reserved_4_value, bytes) =>
                                                  Some ({| badge := badge_value; message_id := message_id_value; instrument_id := instrument_id_value; msar_type := msar_type_value; auction_id := auction_id_value; price := price_value; side := side_value; debit_credit := debit_credit_value; contracts := contracts_value; price_protection := price_protection_value; reserved_4 := reserved_4_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexMsarRequestMessage.

End NtxOptionsQuotingV90Client.
