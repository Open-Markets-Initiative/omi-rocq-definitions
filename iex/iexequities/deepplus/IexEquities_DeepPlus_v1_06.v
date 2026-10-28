From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Investors Exchange DeepPlus

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

Module IexEquitiesDeepPlusV106.

  Module MessageHeader.

    (** Snap message header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module SnapshotRequestMessage.

    (** The Snapshot Request message is sent from the client to the Deep Plus Snap server to authenticate and request a Snapshot Response *)
    Record t := {
      authentication_token : list byte;
      channel_id : N;
      session_id : N;
      minimum_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (authentication_token record) = 40 /\
      (channel_id record < 256 ^ N.of_nat 4)%N /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (minimum_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 40 (authentication_token record) ++
      encode_uint 4 (channel_id record) ++
      encode_uint 4 (session_id record) ++
      encode_uint 8 (minimum_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 40 bytes with
      | None => None
      | Some (authentication_token_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (channel_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (minimum_sequence_number_value, bytes) =>
                      Some ({| authentication_token := authentication_token_value; channel_id := channel_id_value; session_id := session_id_value; minimum_sequence_number := minimum_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SnapshotRequestMessage.

  Module ErrorResponseMessage.

    (** Sent by the Deep Plus Snap server to the client when a Snapshot Request is rejected *)
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

  End ErrorResponseMessage.

  Module SnapshotStartMessage.

    (** First message of a Snapshot Response sent from the Deep Plus Snap server when a Snapshot Request is successful *)
    Record t := {
      snapshot_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (snapshot_length record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (snapshot_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (snapshot_length_value, bytes) =>
          Some ({| snapshot_length := snapshot_length_value |}, bytes)
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

  End SnapshotStartMessage.

  Module IextpHeader.

    (** IexTp header of the wrapped feed message *)
    Record t := {
      version : N;
      reserved : N;
      message_protocol_id : N;
      channel_id : N;
      session_id : N;
      payload_length : N;
      message_count : N;
      stream_offset : N;
      first_message_sequence_number : N;
      send_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N /\
      (reserved record < 256 ^ N.of_nat 1)%N /\
      (message_protocol_id record < 256 ^ N.of_nat 2)%N /\
      (channel_id record < 256 ^ N.of_nat 4)%N /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (payload_length record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N /\
      (stream_offset record < 256 ^ N.of_nat 8)%N /\
      (first_message_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_uint 1 (reserved record) ++
      encode_uint 2 (message_protocol_id record) ++
      encode_uint 4 (channel_id record) ++
      encode_uint 4 (session_id record) ++
      encode_uint 2 (payload_length record) ++
      encode_uint 2 (message_count record) ++
      encode_uint 8 (stream_offset record) ++
      encode_uint 8 (first_message_sequence_number record) ++
      encode_uint 8 (send_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (reserved_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_protocol_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (session_id_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (payload_length_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (message_count_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (stream_offset_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (first_message_sequence_number_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (send_time_value, bytes) =>
                                              Some ({| version := version_value; reserved := reserved_value; message_protocol_id := message_protocol_id_value; channel_id := channel_id_value; session_id := session_id_value; payload_length := payload_length_value; message_count := message_count_value; stream_offset := stream_offset_value; first_message_sequence_number := first_message_sequence_number_value; send_time := send_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End IextpHeader.

  Module SystemEventMessage.

    (** The System Event Message is used to indicate events that apply to the market or the data feed. *)
    Record t := {
      system_event : list byte;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (system_event record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (system_event record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (system_event_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              Some ({| system_event := system_event_value; timestamp := timestamp_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module TradingStatusMessage.

    (** The Trading Status Message is used to indicate the current trading status of a security. *)
    Record t := {
      trading_status : list byte;
      timestamp : N;
      symbol : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_status record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_status record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_status_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      Some ({| trading_status := trading_status_value; timestamp := timestamp_value; symbol := symbol_value; reason := reason_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module RetailLiquidityIndicatorMessage.

    (** broadcasts a real-time Retail Liquidity Indicator Message each time there is an update to IEX's eligible retail liquidity interest during the trading day *)
    Record t := {
      retail_liquidity_indicator : list byte;
      timestamp : N;
      symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (retail_liquidity_indicator record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (retail_liquidity_indicator record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (retail_liquidity_indicator_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  Some ({| retail_liquidity_indicator := retail_liquidity_indicator_value; timestamp := timestamp_value; symbol := symbol_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End RetailLiquidityIndicatorMessage.

  Module OperationalHaltStatusMessage.

    (** The Exchange may suspend trading of one or more securities on IEX for operational reasons and indicates such operational halt using the Operational Halt Status Message. *)
    Record t := {
      operational_halt_status : list byte;
      timestamp : N;
      symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (operational_halt_status record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (operational_halt_status record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (operational_halt_status_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  Some ({| operational_halt_status := operational_halt_status_value; timestamp := timestamp_value; symbol := symbol_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End OperationalHaltStatusMessage.

  Module ShortSalePriceTestStatusMessage.

    (** The Short Sale Price Test Message is used to indicate when a short sale price test restriction is in effect for a security. *)
    Record t := {
      short_sale_price_test_status : N;
      timestamp : N;
      symbol : list byte;
      detail : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (short_sale_price_test_status record < 256 ^ N.of_nat 1)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (detail record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (short_sale_price_test_status record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (detail record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (short_sale_price_test_status_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (detail_value, bytes) =>
                      Some ({| short_sale_price_test_status := short_sale_price_test_status_value; timestamp := timestamp_value; symbol := symbol_value; detail := detail_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortSalePriceTestStatusMessage.

  Module SecurityEventMessage.

    (** The Security Event Message is used to indicate events that apply to a security *)
    Record t := {
      security_event : list byte;
      timestamp : N;
      symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (security_event record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (security_event record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (security_event_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  Some ({| security_event := security_event_value; timestamp := timestamp_value; symbol := symbol_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End SecurityEventMessage.

  Module AddOrderMessage.

    (** A displayed order that has been added to the IEX Book *)
    Record t := {
      side : list byte;
      timestamp : N;
      symbol : list byte;
      order_id : N;
      size : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (side record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (side record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (size record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (side_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (size_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              Some ({| side := side_value; timestamp := timestamp_value; symbol := symbol_value; order_id := order_id_value; size := size_value; price := price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module OrderDeleteMessage.

    (** A displayed order that was removed from the IEX Book *)
    Record t := {
      reserved_1 : list byte;
      timestamp : N;
      symbol : list byte;
      order_id_reference : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (order_id_reference record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 8 (order_id_reference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_reference_value, bytes) =>
                      Some ({| reserved_1 := reserved_1_value; timestamp := timestamp_value; symbol := symbol_value; order_id_reference := order_id_reference_value |}, bytes)
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

  End OrderDeleteMessage.

  Module ClearBookMessage.

    (** This message is used to indicate that the IEX Book for a symbol has been cleared of all orders *)
    Record t := {
      reserved_1 : list byte;
      timestamp : N;
      symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_1 record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved_1 record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  Some ({| reserved_1 := reserved_1_value; timestamp := timestamp_value; symbol := symbol_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End ClearBookMessage.

  Module SnapshotEndMessage.

    (** Final message of a Snapshot Response, carries the sequence number at which the snapshot was created *)
    Record t := {
      snapshot_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (snapshot_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (snapshot_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (snapshot_sequence_number_value, bytes) =>
          Some ({| snapshot_sequence_number := snapshot_sequence_number_value |}, bytes)
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

  End SnapshotEndMessage.

End IexEquitiesDeepPlusV106.
