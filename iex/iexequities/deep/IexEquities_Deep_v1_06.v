From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Investors Exchange Depth Of Book

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
      - the dispatch that chooses a message by its type
      - a run counted by a field
      - a field read in bits
  *)

Module IexEquitiesDeepV106.

  Module IextpHeader.

    (** IexTp packet header *)
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

  Module MessageHeader.

    (** IexTp message header *)
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

  Module PriceLevelBuyUpdateMessage.

    (** Deep broadcasts a real-time Price Level Update Message each time a displayed price level on IEX is updated during the trading day *)
    Record t := {
      event_flags : N;
      timestamp : N;
      symbol : list byte;
      size : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (event_flags record < 256 ^ N.of_nat 1)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (event_flags record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (size record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (event_flags_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (size_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| event_flags := event_flags_value; timestamp := timestamp_value; symbol := symbol_value; size := size_value; price := price_value |}, bytes)
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

  End PriceLevelBuyUpdateMessage.

  Module PriceLevelSellUpdateMessage.

    (** Deep broadcasts a real-time Price Level Update Message each time a displayed price level on IEX is updated during the trading day *)
    Record t := {
      event_flags : N;
      timestamp : N;
      symbol : list byte;
      size : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (event_flags record < 256 ^ N.of_nat 1)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (event_flags record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (size record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (event_flags_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (size_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| event_flags := event_flags_value; timestamp := timestamp_value; symbol := symbol_value; size := size_value; price := price_value |}, bytes)
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

  End PriceLevelSellUpdateMessage.

  Module OfficialPriceMessage.

    (** Official Price Messages are sent for each IEX-listed security to indicate the IEX Official Opening Price and IEX Official Closing Price. *)
    Record t := {
      price_type : list byte;
      timestamp : N;
      symbol : list byte;
      official_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (price_type record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (official_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (price_type record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 8 (official_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (price_type_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (official_price_value, bytes) =>
                      Some ({| price_type := price_type_value; timestamp := timestamp_value; symbol := symbol_value; official_price := official_price_value |}, bytes)
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

  End OfficialPriceMessage.

  Module AuctionInformationMessage.

    (** Broadcasts an Auction Information Message every one second between the Lock-in Time and the auction match for Opening and Closing Auctions, and during the Display Only Period for IPO, Halt, and Volatility Auctions. *)
    Record t := {
      auction_type : list byte;
      timestamp : N;
      symbol : list byte;
      paired_shares : N;
      reference_price : N;
      indicative_clearing_price : N;
      imbalance_shares : N;
      imbalance_side : list byte;
      extension_number : list byte;
      scheduled_auction_time : N;
      auction_book_clearing_price : N;
      collar_reference_price : N;
      lower_auction_collar : N;
      upper_auction_collar : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (auction_type record) = 1 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (paired_shares record < 256 ^ N.of_nat 4)%N /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (indicative_clearing_price record < 256 ^ N.of_nat 8)%N /\
      (imbalance_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (imbalance_side record) = 1 /\
      Datatypes.length (extension_number record) = 1 /\
      (scheduled_auction_time record < 256 ^ N.of_nat 4)%N /\
      (auction_book_clearing_price record < 256 ^ N.of_nat 8)%N /\
      (collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (lower_auction_collar record < 256 ^ N.of_nat 8)%N /\
      (upper_auction_collar record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (paired_shares record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (indicative_clearing_price record) ++
      encode_uint 4 (imbalance_shares record) ++
      encode_bytes 1 (imbalance_side record) ++
      encode_bytes 1 (extension_number record) ++
      encode_uint 4 (scheduled_auction_time record) ++
      encode_uint 8 (auction_book_clearing_price record) ++
      encode_uint 8 (collar_reference_price record) ++
      encode_uint 8 (lower_auction_collar record) ++
      encode_uint 8 (upper_auction_collar record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (auction_type_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (paired_shares_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (reference_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (indicative_clearing_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (imbalance_shares_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (imbalance_side_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (extension_number_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (scheduled_auction_time_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (auction_book_clearing_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (collar_reference_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (lower_auction_collar_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (upper_auction_collar_value, bytes) =>
                                                              Some ({| auction_type := auction_type_value; timestamp := timestamp_value; symbol := symbol_value; paired_shares := paired_shares_value; reference_price := reference_price_value; indicative_clearing_price := indicative_clearing_price_value; imbalance_shares := imbalance_shares_value; imbalance_side := imbalance_side_value; extension_number := extension_number_value; scheduled_auction_time := scheduled_auction_time_value; auction_book_clearing_price := auction_book_clearing_price_value; collar_reference_price := collar_reference_price_value; lower_auction_collar := lower_auction_collar_value; upper_auction_collar := upper_auction_collar_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
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

  End AuctionInformationMessage.

End IexEquitiesDeepV106.
