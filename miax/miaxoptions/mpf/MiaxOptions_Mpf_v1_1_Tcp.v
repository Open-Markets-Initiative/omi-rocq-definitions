From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings MIAX Product Feed

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

Module MiaxOptionsMpfV11Tcp.

  Module SesmPacketHeader.

    (** SesM packet header *)
    Record t := {
      sesm_packet_length : N;
      sesm_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sesm_packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sesm_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (sesm_packet_length record) ++
      encode_bytes 1 (sesm_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (sesm_packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sesm_packet_type_value, bytes) =>
              Some ({| sesm_packet_length := sesm_packet_length_value; sesm_packet_type := sesm_packet_type_value |}, bytes)
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

  End SesmPacketHeader.

  Module RefreshRequestMessage.

    (** Sent by the firm over the MPF Retransmission Interface (SesM Unsequenced Data Packet) to request a Last Value Refresh of a particular data set identified by Refresh Message Type. *)
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

  Module SymbolDefinitionMessage.

    (** This is the message format that will be used to disseminate all Synthetic Future symbol definitions for the current session. *)
    Record t := {
      nanoseconds : N;
      synthetic_future_symbol : list byte;
      settlement_date : list byte;
      symbol_status : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (synthetic_future_symbol record) = 8 /\
      Datatypes.length (settlement_date record) = 8 /\
      Datatypes.length (symbol_status record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (synthetic_future_symbol record) ++
      encode_bytes 8 (settlement_date record) ++
      encode_bytes 1 (symbol_status record) ++
      encode_bytes 16 (reserved_16 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (synthetic_future_symbol_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (settlement_date_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (symbol_status_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (reserved_16_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; synthetic_future_symbol := synthetic_future_symbol_value; settlement_date := settlement_date_value; symbol_status := symbol_status_value; reserved_16 := reserved_16_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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

  End SymbolDefinitionMessage.

  Module IndexValueMessage.

    (** This is the message format that will be used to disseminate current index value. The index value may be the index cash value or the index settlement value, as identified by the Index Symbol. *)
    Record t := {
      nanoseconds : N;
      symbol : list byte;
      value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 5 /\
      (value record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 5 (symbol record) ++
      encode_uint 4 (value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (value_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; symbol := symbol_value; value := value_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexValueMessage.

  Module SyntheticFutureValueMessage.

    (** This is the message format that will be used to disseminate current Synthetic Future values. The specific Synthetic Future value is identified by the Synthetic Future Symbol. *)
    Record t := {
      nanoseconds : N;
      synthetic_future_symbol : list byte;
      value : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (synthetic_future_symbol record) = 8 /\
      (value record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (synthetic_future_symbol record) ++
      encode_uint 4 (value record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (synthetic_future_symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (value_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (reserved_8_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; synthetic_future_symbol := synthetic_future_symbol_value; value := value_value; reserved_8 := reserved_8_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End SyntheticFutureValueMessage.

  Module EndOfRefreshNotificationMessage.

    (** Sent by MIAX Options over the MPF Retransmission Interface (SesM Unsequenced Data Packet) when the refresh response is complete. *)
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
      sesm_version : list byte;
      username : list byte;
      computer_id : list byte;
      application_protocol : list byte;
      requested_trading_session_id : N;
      requested_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sesm_version record) = 5 /\
      Datatypes.length (username record) = 5 /\
      Datatypes.length (computer_id record) = 8 /\
      Datatypes.length (application_protocol record) = 8 /\
      (requested_trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (requested_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (sesm_version record) ++
      encode_bytes 5 (username record) ++
      encode_bytes 8 (computer_id record) ++
      encode_bytes 8 (application_protocol record) ++
      encode_uint 1 (requested_trading_session_id record) ++
      encode_uint 8 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (sesm_version_value, bytes) =>
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
                              Some ({| sesm_version := sesm_version_value; username := username_value; computer_id := computer_id_value; application_protocol := application_protocol_value; requested_trading_session_id := requested_trading_session_id_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
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

    (** The SesM server sends a Login response packet in response a Login request packet from the client *)
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

    (** The SesM client uses this packet to request a retransmission server to retransmit a range of packets *)
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

End MiaxOptionsMpfV11Tcp.
