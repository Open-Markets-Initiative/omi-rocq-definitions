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
      - a run filling what frames it
      - a length prefix framing what follows
  *)

Module PearlEquitiesDepthOfMarketV13DTcp.

  Module EsesmPacketHeader.

    (** ESesM packet header *)
    Record t := {
      esesm_packet_length : N;
      esesm_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (esesm_packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (esesm_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (esesm_packet_length record) ++
      encode_bytes 1 (esesm_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (esesm_packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (esesm_packet_type_value, bytes) =>
              Some ({| esesm_packet_length := esesm_packet_length_value; esesm_packet_type := esesm_packet_type_value |}, bytes)
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

  End EsesmPacketHeader.

  Module RefreshRequestMessage.

    (** Sent by the firm over the DoM Retransmission Interface (ESeSM Unsequenced Data Packet) to request a Last Value Refresh of a particular data set identified by Refresh Message Type. *)
    Record t := {
      refresh_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (refresh_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (refresh_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (refresh_message_type_value, bytes) =>
          Some ({| refresh_message_type := refresh_message_type_value |}, bytes)
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

  End RefreshRequestMessage.

  Module RefreshResponseMessage.

    (** Sent by MIAX Pearl Equities over the DoM Retransmission Interface (ESeSM Unsequenced Data Packet) carrying one Application Message that satisfies a previous Refresh Request. *)
    Record t := {
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          Some ({| sequence_number := sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End RefreshResponseMessage.

  Module EndOfRefreshNotificationMessage.

    (** Sent by MIAX Pearl Equities over the DoM Retransmission Interface (ESeSM Unsequenced Data Packet) when the refresh response is complete. *)
    Record t := {
      refresh_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (refresh_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (refresh_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (refresh_message_type_value, bytes) =>
          Some ({| refresh_message_type := refresh_message_type_value |}, bytes)
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

  End EndOfRefreshNotificationMessage.

  Module LoginRequest.

    (** The SesM client must send a Login request packet immediately upon establishing a new TCP/IP socket connection to the server *)
    Record t := {
      esesm_version : list byte;
      username : list byte;
      computer_id : list byte;
      application_protocol : list byte;
      requested_trading_session_id : N;
      requested_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (esesm_version record) = 5 /\
      Datatypes.length (username record) = 5 /\
      Datatypes.length (computer_id record) = 8 /\
      Datatypes.length (application_protocol record) = 8 /\
      (requested_trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (requested_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (esesm_version record) ++
      encode_bytes 5 (username record) ++
      encode_bytes 8 (computer_id record) ++
      encode_bytes 8 (application_protocol record) ++
      encode_uint 1 (requested_trading_session_id record) ++
      encode_uint 8 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (esesm_version_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (username_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (computer_id_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (application_protocol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (requested_trading_session_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (requested_sequence_number_value, bytes) =>
                              Some ({| esesm_version := esesm_version_value; username := username_value; computer_id := computer_id_value; application_protocol := application_protocol_value; requested_trading_session_id := requested_trading_session_id_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequest.

  Module LoginResponse.

    (** The SesM server sends a Login response packet in response a Login request packet from the client *)
    Record t := {
      number_of_matching_engines : N;
      login_status : list byte;
      trading_session_id : N;
      highest_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_matching_engines record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (login_status record) = 1 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (highest_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (number_of_matching_engines record) ++
      encode_bytes 1 (login_status record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 8 (highest_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (number_of_matching_engines_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (login_status_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (highest_sequence_number_value, bytes) =>
                      Some ({| number_of_matching_engines := number_of_matching_engines_value; login_status := login_status_value; trading_session_id := trading_session_id_value; highest_sequence_number := highest_sequence_number_value |}, bytes)
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

  End LoginResponse.

  Module SynchronizationComplete.

    (** The ESesM server sends a Login response packet in response a Login request packet from the client *)
    Record t := {
      number_of_matching_engines : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_matching_engines record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (number_of_matching_engines record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (number_of_matching_engines_value, bytes) =>
          Some ({| number_of_matching_engines := number_of_matching_engines_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End SynchronizationComplete.

  Module RetransmissionRequest.

    (** The ESesM client uses this packet to request a retransmission server to retransmit a range of packets *)
    Record t := {
      start_sequence_number : N;
      end_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (end_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (start_sequence_number record) ++
      encode_uint 8 (end_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (start_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (end_sequence_number_value, bytes) =>
              Some ({| start_sequence_number := start_sequence_number_value; end_sequence_number := end_sequence_number_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RetransmissionRequest.

End PearlEquitiesDepthOfMarketV13DTcp.
