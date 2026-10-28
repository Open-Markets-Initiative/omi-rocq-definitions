From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Currenex Executable Streaming Prices

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
  *)

Module CurrenexForexEspV9.

  Module MessageHeader.

    (** Currenex Itch Market Data Message Header *)
    Record t := {
      sequence_number : N;
      timestamp : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (timestamp record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  Some ({| sequence_number := sequence_number_value; timestamp := timestamp_value; message_type := message_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End MessageHeader.

  Module Logon.

    (** A MP initiates a session by submitting a Logon message to Currenex *)
    Record t := {
      user_id : list byte;
      password : list byte;
      session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 20 /\
      Datatypes.length (password record) = 20 /\
      (session_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (user_id record) ++
      encode_bytes 20 (password record) ++
      encode_uint 4 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  Some ({| user_id := user_id_value; password := password_value; session_id := session_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Logon.

  Module Logout.

    (** Currenex or a MP can terminate a session by sending a Logout message *)
    Record t := {
      user_id : list byte;
      session_id : N;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 20 /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reason record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (user_id record) ++
      encode_uint 4 (session_id record) ++
      encode_bytes 3 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (reason_value, bytes) =>
                  Some ({| user_id := user_id_value; session_id := session_id_value; reason := reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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

  End Logout.

  Module Heartbeat.

    (** To ensure session integrity, Currenex sends a heartbeat message every fifteen seconds *)
    Record t := {
      session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          Some ({| session_id := session_id_value |}, bytes)
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

  End Heartbeat.

  Module InstrumentInfo.

    (** Included in the InstrumentInfo message is the InstrumentType, a free form instrument definition, and the InstrumentIndex used to request quotes and manage price updates *)
    Record t := {
      session_id : N;
      instrument_index : N;
      instrument_type : list byte;
      instrument_id : list byte;
      settlement_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (instrument_id record) = 20 /\
      (settlement_date record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 2 (instrument_index record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 20 (instrument_id record) ++
      encode_uint 8 (settlement_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (instrument_index_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (instrument_type_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (instrument_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (settlement_date_value, bytes) =>
                          Some ({| session_id := session_id_value; instrument_index := instrument_index_value; instrument_type := instrument_type_value; instrument_id := instrument_id_value; settlement_date := settlement_date_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentInfo.

  Module InstrumentInfoAck.

    (** A MP should respond to each received InstrumentInfo message with an InstrumentInfoAck message *)
    Record t := {
      session_id : N;
      instrument_index : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (instrument_index record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 2 (instrument_index record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (instrument_index_value, bytes) =>
              Some ({| session_id := session_id_value; instrument_index := instrument_index_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End InstrumentInfoAck.

  Module SubscriptionRequest.

    (** Currenex will stream ESP messages to a MP once it receives a SubscriptionRequest message for the pair *)
    Record t := {
      session_id : N;
      subscription_type : list byte;
      instrument_index : N;
      subscribe_to_ticker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (subscription_type record) = 1 /\
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (subscribe_to_ticker record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (subscription_type record) ++
      encode_uint 2 (instrument_index record) ++
      encode_bytes 1 (subscribe_to_ticker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (subscription_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (instrument_index_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (subscribe_to_ticker_value, bytes) =>
                      Some ({| session_id := session_id_value; subscription_type := subscription_type_value; instrument_index := instrument_index_value; subscribe_to_ticker := subscribe_to_ticker_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End SubscriptionRequest.

  Module SubscriptionReply.

    (** Currenex responds to a SubscriptionRequest with a SubscriptionReply message *)
    Record t := {
      session_id : N;
      instrument_index : N;
      reply_type : list byte;
      reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reply_type record) = 1 /\
      Datatypes.length (reject_reason record) = 50.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 2 (instrument_index record) ++
      encode_bytes 1 (reply_type record) ++
      encode_bytes 50 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (instrument_index_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reply_type_value, bytes) =>
                  match decode_bytes 50 bytes with
                  | None => None
                  | Some (reject_reason_value, bytes) =>
                      Some ({| session_id := session_id_value; instrument_index := instrument_index_value; reply_type := reply_type_value; reject_reason := reject_reason_value |}, bytes)
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

  End SubscriptionReply.

  Module PriceMessage.

    (** Price Message *)
    Record t := {
      instrument_index : N;
      price_id : N;
      side : list byte;
      max_amount : N;
      min_amount : N;
      price : N;
      attributed : list byte;
      price_provider : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      (price_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side record) = 1 /\
      (max_amount record < 256 ^ N.of_nat 8)%N /\
      (min_amount record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (attributed record) = 1 /\
      Datatypes.length (price_provider record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (instrument_index record) ++
      encode_uint 1 (price_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (max_amount record) ++
      encode_uint 8 (min_amount record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (attributed record) ++
      encode_bytes 4 (price_provider record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (instrument_index_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (price_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (max_amount_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (min_amount_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (attributed_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (price_provider_value, bytes) =>
                                      Some ({| instrument_index := instrument_index_value; price_id := price_id_value; side := side_value; max_amount := max_amount_value; min_amount := min_amount_value; price := price_value; attributed := attributed_value; price_provider := price_provider_value |}, bytes)
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceMessage.

  Module PriceCancelMessage.

    (** Price Cancel *)
    Record t := {
      instrument_index : N;
      price_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      (price_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (instrument_index record) ++
      encode_uint 1 (price_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (instrument_index_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (price_id_value, bytes) =>
              Some ({| instrument_index := instrument_index_value; price_id := price_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End PriceCancelMessage.

  Module TradeTickerMessage.

    (** A MP can subscribe to TradeTicker messages by setting SubscribeToTicker=0 in the SubscriptionRequest message *)
    Record t := {
      instrument_index : N;
      rate : N;
      ticker_type : list byte;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      (rate record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ticker_type record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (instrument_index record) ++
      encode_uint 4 (rate record) ++
      encode_bytes 1 (ticker_type record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (instrument_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (rate_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (ticker_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transact_time_value, bytes) =>
                      Some ({| instrument_index := instrument_index_value; rate := rate_value; ticker_type := ticker_type_value; transact_time := transact_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End TradeTickerMessage.

  Module RejectMessage.

    (** Included in the InstrumentInfo message is the InstrumentType, a free form instrument definition, and the InstrumentIndex used to request quotes and manage price updates *)
    Record t := {
      session_id : N;
      reject_msg_type : list byte;
      reject_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reject_msg_type record) = 1 /\
      Datatypes.length (reject_reason record) = 50.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (reject_msg_type record) ++
      encode_bytes 50 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reject_msg_type_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (reject_reason_value, bytes) =>
                  Some ({| session_id := session_id_value; reject_msg_type := reject_msg_type_value; reject_reason := reject_reason_value |}, bytes)
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

  End RejectMessage.

End CurrenexForexEspV9.
