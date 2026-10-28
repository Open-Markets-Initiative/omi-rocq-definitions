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

Module NomOptionsQuotingV90Server.

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

  Module MsarAcceptMessage.

    (** The MSAR Request was accepted by the matching engine. Sequenced. *)
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

  End MsarAcceptMessage.

  Module MsarRejectMessage.

    (** The MSAR Request is invalid and therefore rejected. Sequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      status_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 1 (status_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_code_value, bytes) =>
                  Some ({| badge := badge_value; message_id := message_id_value; status_code := status_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End MsarRejectMessage.

  Module ComplexMsarAcceptMessage.

    (** The Complex MSAR Request was accepted by the matching engine. Sequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      instrument_id : N;
      msar_type : list byte;
      auction_id : N;
      price : N;
      side : list byte;
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
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (contracts_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (price_protection_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (reserved_4_value, bytes) =>
                                              Some ({| badge := badge_value; message_id := message_id_value; instrument_id := instrument_id_value; msar_type := msar_type_value; auction_id := auction_id_value; price := price_value; side := side_value; contracts := contracts_value; price_protection := price_protection_value; reserved_4 := reserved_4_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexMsarAcceptMessage.

  Module ComplexMsarRejectMessage.

    (** The Complex MSAR Request is invalid and therefore rejected. Sequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      status_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 1 (status_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_code_value, bytes) =>
                  Some ({| badge := badge_value; message_id := message_id_value; status_code := status_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End ComplexMsarRejectMessage.

  Module UnderlyingPermissionNotificationMessage.

    (** Sent once per badge/underlying pair, typically right after the instrument directory messages, and intra-day when permissions change. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      underlying : list byte;
      permitted : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (underlying record) = 13 /\
      Datatypes.length (permitted record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_bytes 13 (underlying record) ++
      encode_bytes 1 (permitted record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (underlying_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (permitted_value, bytes) =>
                          Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; underlying := underlying_value; permitted := permitted_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingPermissionNotificationMessage.

  Module MmParameterDefinitionNotificationMessage.

    (** Optionally delivered participant per-underlying/instrument type configuration settings. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
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
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (underlying record) = 13 /\
      (interval record < 256 ^ N.of_nat 2)%N /\
      (percentage record < 256 ^ N.of_nat 2)%N /\
      (cum_qty record < 256 ^ N.of_nat 4)%N /\
      (delta record < 256 ^ N.of_nat 4)%N /\
      (vega record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_32 record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 13 (underlying record) ++
      encode_uint 2 (interval record) ++
      encode_uint 2 (percentage record) ++
      encode_uint 4 (cum_qty record) ++
      encode_uint 4 (delta record) ++
      encode_uint 4 (vega record) ++
      encode_bytes 32 (reserved_32 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
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
                                                  Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; instrument_type := instrument_type_value; underlying := underlying_value; interval := interval_value; percentage := percentage_value; cum_qty := cum_qty_value; delta := delta_value; vega := vega_value; reserved_32 := reserved_32_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MmParameterDefinitionNotificationMessage.

  Module RapidFireConfigNotificationMessage.

    (** Rapid Fire/Curtailment Config Notification, Phlx, NOM and NTX only (replaced by MM Parameter Definition Notification for ISE, GEMX and MRX). Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      underlying : list byte;
      percentage : N;
      interval : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (underlying record) = 13 /\
      (percentage record < 256 ^ N.of_nat 2)%N /\
      (interval record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_bytes 13 (underlying record) ++
      encode_uint 2 (percentage record) ++
      encode_uint 2 (interval record) ++
      encode_uint 4 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (underlying_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (percentage_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (interval_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; underlying := underlying_value; percentage := percentage_value; interval := interval_value; volume := volume_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RapidFireConfigNotificationMessage.

  Module ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage.

    (** Optionally delivered contract limit on the badges configured for ActiveQP. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      underlying : list byte;
      set_contract_limit : N;
      reserved_32 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (underlying record) = 13 /\
      (set_contract_limit record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_32 record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_bytes 13 (underlying record) ++
      encode_uint 4 (set_contract_limit record) ++
      encode_bytes 32 (reserved_32 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (underlying_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (set_contract_limit_value, bytes) =>
                          match decode_bytes 32 bytes with
                          | None => None
                          | Some (reserved_32_value, bytes) =>
                              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; underlying := underlying_value; set_contract_limit := set_contract_limit_value; reserved_32 := reserved_32_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveQpSelfReplenishmentParameterDefinitionNotificationMessage.

  Module SystemEventMessage.

    (** Signals a market or data feed handler event. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      event_code : list byte;
      version : N;
      sub_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1 /\
      (version record < 256 ^ N.of_nat 1)%N /\
      (sub_version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 1 (version record) ++
      encode_uint 1 (sub_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (sub_version_value, bytes) =>
                          Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; event_code := event_code_value; version := version_value; sub_version := sub_version_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module SimpleInstrumentDirectoryMessage.

    (** Disseminated at the start of each trading day for all symbols trading on the system, and intra-day when attributes change. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      instrument_id : N;
      security_symbol : list byte;
      expiration : N;
      strike_price : N;
      option_type : list byte;
      underlying_symbol : list byte;
      closing_type : list byte;
      tradable : list byte;
      mpv : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_symbol record) = 8 /\
      (expiration record < 256 ^ N.of_nat 2)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (closing_type record) = 1 /\
      Datatypes.length (tradable record) = 1 /\
      Datatypes.length (mpv record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 8 (security_symbol record) ++
      encode_uint 2 (expiration record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (closing_type record) ++
      encode_bytes 1 (tradable record) ++
      encode_bytes 1 (mpv record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (security_symbol_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (expiration_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
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
                                                      Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; instrument_id := instrument_id_value; security_symbol := security_symbol_value; expiration := expiration_value; strike_price := strike_price_value; option_type := option_type_value; underlying_symbol := underlying_symbol_value; closing_type := closing_type_value; tradable := tradable_value; mpv := mpv_value; reserved_16 := reserved_16_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleInstrumentDirectoryMessage.

  Module SimpleInstrumentTradingActionMessage.

    (** Relays changes in trading status for a simple instrument. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      instrument_id : N;
      trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_state_value, bytes) =>
                      Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; instrument_id := instrument_id_value; trading_state := trading_state_value |}, bytes)
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

  End SimpleInstrumentTradingActionMessage.

  Module ComplexInstrumentTradingActionMessage.

    (** Relays changes in trading status for a complex strategy. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      instrument_id : N;
      trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_state_value, bytes) =>
                      Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; instrument_id := instrument_id_value; trading_state := trading_state_value |}, bytes)
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

  End ComplexInstrumentTradingActionMessage.

  Module SimpleQuoteExecutionNotificationMessage.

    (** Informs the firm that its quote for a given simple instrument has been executed. Only sent if subscribed. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      instrument_id : N;
      message_id : N;
      auction_id : N;
      price : N;
      side : list byte;
      contracts : N;
      liquidity_indicator : N;
      cross_id : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (liquidity_indicator record < 256 ^ N.of_nat 1)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (contracts record) ++
      encode_uint 1 (liquidity_indicator record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (message_id_value, bytes) =>
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
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (liquidity_indicator_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (cross_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (match_id_value, bytes) =>
                                                      Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; instrument_id := instrument_id_value; message_id := message_id_value; auction_id := auction_id_value; price := price_value; side := side_value; contracts := contracts_value; liquidity_indicator := liquidity_indicator_value; cross_id := cross_id_value; match_id := match_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleQuoteExecutionNotificationMessage.

  Module ComplexQuoteExecutionNotificationMessage.

    (** Informs the participant that its quote for a given complex instrument has been executed. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      message_id : N;
      instrument_id : N;
      auction_id : N;
      price_6 : N;
      side : list byte;
      contracts : N;
      liquidity_indicator : N;
      cross_id : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price_6 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (liquidity_indicator record < 256 ^ N.of_nat 1)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 8 (price_6 record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (contracts record) ++
      encode_uint 1 (liquidity_indicator record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (message_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (auction_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_6_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (contracts_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (liquidity_indicator_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (cross_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (match_id_value, bytes) =>
                                                      Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; message_id := message_id_value; instrument_id := instrument_id_value; auction_id := auction_id_value; price_6 := price_6_value; side := side_value; contracts := contracts_value; liquidity_indicator := liquidity_indicator_value; cross_id := cross_id_value; match_id := match_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexQuoteExecutionNotificationMessage.

  Module ComplexQuoteLegExecutionNotificationMessage.

    (** Leg level execution of a quote in a complex instrument. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      message_id : N;
      instrument_id : N;
      leg_instrument_id : N;
      leg_id : N;
      auction_id : N;
      price_6 : N;
      side : list byte;
      contracts : N;
      liquidity_indicator : N;
      cross_id : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_id record < 256 ^ N.of_nat 1)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price_6 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (liquidity_indicator record < 256 ^ N.of_nat 1)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (leg_instrument_id record) ++
      encode_uint 1 (leg_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 8 (price_6 record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (contracts record) ++
      encode_uint 1 (liquidity_indicator record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (message_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leg_instrument_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (leg_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (auction_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_6_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (side_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (contracts_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (liquidity_indicator_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (cross_id_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (match_id_value, bytes) =>
                                                              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; message_id := message_id_value; instrument_id := instrument_id_value; leg_instrument_id := leg_instrument_id_value; leg_id := leg_id_value; auction_id := auction_id_value; price_6 := price_6_value; side := side_value; contracts := contracts_value; liquidity_indicator := liquidity_indicator_value; cross_id := cross_id_value; match_id := match_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexQuoteLegExecutionNotificationMessage.

  Module SimpleMsarNotificationMessage.

    (** Execution Notification Message: the MSAR Request for a given simple instrument has been executed or cancelled. The Side field reflects the side being swept. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      instrument_id : N;
      notification_type : list byte;
      message_id : N;
      auction_id : N;
      price : N;
      side : list byte;
      contracts : N;
      liquidity_indicator : N;
      cross_id : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (notification_type record) = 1 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (liquidity_indicator record < 256 ^ N.of_nat 1)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (notification_type record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (contracts record) ++
      encode_uint 1 (liquidity_indicator record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (notification_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (message_id_value, bytes) =>
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
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (liquidity_indicator_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (cross_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (match_id_value, bytes) =>
                                                          Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; instrument_id := instrument_id_value; notification_type := notification_type_value; message_id := message_id_value; auction_id := auction_id_value; price := price_value; side := side_value; contracts := contracts_value; liquidity_indicator := liquidity_indicator_value; cross_id := cross_id_value; match_id := match_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleMsarNotificationMessage.

  Module ComplexMsarLegNotificationMessage.

    (** Leg-level information on the execution/out of an MSAR for a complex instrument. Precedes the corresponding Complex MSAR Notification. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      instrument_id : N;
      leg_id : N;
      leg_instrument_id : N;
      notification_type : list byte;
      message_id : N;
      auction_id : N;
      price : N;
      side : list byte;
      leg_side : list byte;
      contracts : N;
      liquidity_indicator : N;
      cross_id : N;
      match_id : N;
      price_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_id record < 256 ^ N.of_nat 1)%N /\
      (leg_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (notification_type record) = 1 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (leg_side record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (liquidity_indicator record < 256 ^ N.of_nat 1)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N /\
      (price_6 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (leg_id record) ++
      encode_uint 4 (leg_instrument_id record) ++
      encode_bytes 1 (notification_type record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (leg_side record) ++
      encode_uint 4 (contracts record) ++
      encode_uint 1 (liquidity_indicator record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record) ++
      encode_uint 8 (price_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (leg_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leg_instrument_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (notification_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (message_id_value, bytes) =>
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
                                                  | Some (leg_side_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (contracts_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (liquidity_indicator_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (cross_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (match_id_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (price_6_value, bytes) =>
                                                                          Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; instrument_id := instrument_id_value; leg_id := leg_id_value; leg_instrument_id := leg_instrument_id_value; notification_type := notification_type_value; message_id := message_id_value; auction_id := auction_id_value; price := price_value; side := side_value; leg_side := leg_side_value; contracts := contracts_value; liquidity_indicator := liquidity_indicator_value; cross_id := cross_id_value; match_id := match_id_value; price_6 := price_6_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexMsarLegNotificationMessage.

  Module ComplexMsarNotificationMessage.

    (** Complex MSAR Execution Notification: the Complex MSAR Request has been executed or cancelled. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      instrument_id : N;
      notification_type : list byte;
      message_id : N;
      auction_id : N;
      price : N;
      side : list byte;
      contracts : N;
      liquidity_indicator : N;
      cross_id : N;
      match_id : N;
      price_6 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (notification_type record) = 1 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (liquidity_indicator record < 256 ^ N.of_nat 1)%N /\
      (cross_id record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 4)%N /\
      (price_6 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (notification_type record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (contracts record) ++
      encode_uint 1 (liquidity_indicator record) ++
      encode_uint 4 (cross_id record) ++
      encode_uint 4 (match_id record) ++
      encode_uint 8 (price_6 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (instrument_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (notification_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (message_id_value, bytes) =>
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
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (liquidity_indicator_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (cross_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (match_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (price_6_value, bytes) =>
                                                              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; instrument_id := instrument_id_value; notification_type := notification_type_value; message_id := message_id_value; auction_id := auction_id_value; price := price_value; side := side_value; contracts := contracts_value; liquidity_indicator := liquidity_indicator_value; cross_id := cross_id_value; match_id := match_id_value; price_6 := price_6_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexMsarNotificationMessage.

  Module OpeningRotationQuoteSpreadMultiplierNotificationMessage.

    (** Quote Spread Multiplier Message: sent once per underlying permitted on the port and whenever the effective multiplier changes intraday. Sequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      underlying_symbol : list byte;
      multiplier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      (multiplier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_uint 1 (multiplier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (multiplier_value, bytes) =>
                      Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; underlying_symbol := underlying_symbol_value; multiplier := multiplier_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningRotationQuoteSpreadMultiplierNotificationMessage.

  Module NotificationSubscriptionReplyMessage.

    (** Reply to a Notification Subscription Request. Unsequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      status_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 1 (status_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_code_value, bytes) =>
                  Some ({| badge := badge_value; message_id := message_id_value; status_code := status_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End NotificationSubscriptionReplyMessage.

  Module AddComplexInstrumentReplyMessage.

    (** Response to the Add Complex Instrument Request (AC) indicating the validity of the request. Unsequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      status_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 1 (status_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_code_value, bytes) =>
                  Some ({| badge := badge_value; message_id := message_id_value; status_code := status_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End AddComplexInstrumentReplyMessage.

  Module MmParameterDefinitionReplyMessage.

    (** Response to the MM Parameter Definition Request (AE) indicating the validity of the request. Unsequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      status_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 1 (status_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_code_value, bytes) =>
                  Some ({| badge := badge_value; message_id := message_id_value; status_code := status_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End MmParameterDefinitionReplyMessage.

  Module ActiveQpSelfReplenishmentSetLimitReplyMessage.

    (** Acknowledgement message for Set Limit Message. Unsequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      underlying_symbol : list byte;
      set_value : N;
      status_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      (set_value record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (status_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_uint 4 (set_value record) ++
      encode_bytes 1 (status_code record).

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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (status_code_value, bytes) =>
                          Some ({| badge := badge_value; message_id := message_id_value; underlying_symbol := underlying_symbol_value; set_value := set_value_value; status_code := status_code_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveQpSelfReplenishmentSetLimitReplyMessage.

  Module RapidFireConfigReplyMessage.

    (** Rapid-Fire Config Reply Message. Unsequenced. *)
    Record t := {
      badge : list byte;
      status_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (status_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_bytes 1 (status_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (status_code_value, bytes) =>
              Some ({| badge := badge_value; status_code := status_code_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End RapidFireConfigReplyMessage.

  Module UnderlyingPurgeReplyMessage.

    (** Underlying Purge Reply Message including SentTimestamp. Unsequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      sent_timestamp : N;
      status_code : list byte;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (sent_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status_code record) = 1 /\
      (sequence record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 8 (sent_timestamp record) ++
      encode_bytes 1 (status_code record) ++
      encode_uint 8 (sequence record).

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
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (status_code_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sequence_value, bytes) =>
                          Some ({| badge := badge_value; message_id := message_id_value; sent_timestamp := sent_timestamp_value; status_code := status_code_value; sequence := sequence_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingPurgeReplyMessage.

  Module MarketReentryReplyMessage.

    (** Market Reentry Reply Message. Unsequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      status_code : list byte;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status_code record) = 1 /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 1 (status_code record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (badge_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_code_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (reserved_8_value, bytes) =>
                      Some ({| badge := badge_value; message_id := message_id_value; status_code := status_code_value; reserved_8 := reserved_8_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End MarketReentryReplyMessage.

  Module ActiveQpSelfReplenishmentRequestReentryReplyMessage.

    (** Acknowledgement for the ActiveQP Request/Reentry Message. Unsequenced. *)
    Record t := {
      badge : list byte;
      message_id : N;
      underlying_symbol : list byte;
      status_code : list byte;
      requested_replenishment_value : N;
      active_counter_value : N;
      set_contract_limit : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (status_code record) = 1 /\
      (requested_replenishment_value record < 256 ^ N.of_nat 4)%N /\
      (active_counter_value record < 256 ^ N.of_nat 4)%N /\
      (set_contract_limit record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (status_code record) ++
      encode_uint 4 (requested_replenishment_value record) ++
      encode_uint 4 (active_counter_value record) ++
      encode_uint 4 (set_contract_limit record).

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
                  | Some (status_code_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (requested_replenishment_value_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (active_counter_value_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (set_contract_limit_value, bytes) =>
                                  Some ({| badge := badge_value; message_id := message_id_value; underlying_symbol := underlying_symbol_value; status_code := status_code_value; requested_replenishment_value := requested_replenishment_value_value; active_counter_value := active_counter_value_value; set_contract_limit := set_contract_limit_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveQpSelfReplenishmentRequestReentryReplyMessage.

  Module InstrumentPurgeNotificationMessage.

    (** Informs the firm that its quotes for a given simple or complex instrument have been purged. Unsequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      message_id : N;
      instrument_id : N;
      purge_reason : list byte;
      sequence : N;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (purge_reason record) = 1 /\
      (sequence record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (purge_reason record) ++
      encode_uint 8 (sequence record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
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
                          | Some (purge_reason_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (sequence_value, bytes) =>
                                  match decode_bytes 16 bytes with
                                  | None => None
                                  | Some (reserved_16_value, bytes) =>
                                      Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; message_id := message_id_value; instrument_id := instrument_id_value; purge_reason := purge_reason_value; sequence := sequence_value; reserved_16 := reserved_16_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentPurgeNotificationMessage.

  Module UnderlyingPurgeNotificationMessage.

    (** Informs the firm that all the quotes for instruments associated with the given underlying have been purged (user request, Rapid Fire/ActiveQP risk protection or Kill-Switch). Unsequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      underlying : list byte;
      purge_reason : list byte;
      message_id : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (underlying record) = 13 /\
      Datatypes.length (purge_reason record) = 1 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (sequence record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_bytes 13 (underlying record) ++
      encode_bytes 1 (purge_reason record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 8 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (underlying_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (purge_reason_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (message_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (sequence_value, bytes) =>
                                  Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; underlying := underlying_value; purge_reason := purge_reason_value; message_id := message_id_value; sequence := sequence_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingPurgeNotificationMessage.

  Module MarketReentryNotificationMessage.

    (** Informs that risk protection triggered by rapid fire/purge has been reset for the specified scope. Unsequenced. *)
    Record t := {
      seconds : N;
      nanoseconds : N;
      badge : list byte;
      underlying_symbol : list byte;
      reentry_scope : list byte;
      message_id : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (badge record) = 4 /\
      Datatypes.length (underlying_symbol record) = 13 /\
      Datatypes.length (reentry_scope record) = 1 /\
      (message_id record < 256 ^ N.of_nat 8)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 4 (badge record) ++
      encode_bytes 13 (underlying_symbol record) ++
      encode_bytes 1 (reentry_scope record) ++
      encode_uint 8 (message_id record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (badge_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (underlying_symbol_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reentry_scope_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (message_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (reserved_8_value, bytes) =>
                                  Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value; badge := badge_value; underlying_symbol := underlying_symbol_value; reentry_scope := reentry_scope_value; message_id := message_id_value; reserved_8 := reserved_8_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketReentryNotificationMessage.

End NomOptionsQuotingV90Server.
