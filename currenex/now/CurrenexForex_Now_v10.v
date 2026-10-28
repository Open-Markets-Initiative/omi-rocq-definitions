From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Currenex Now Forex Market Data

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
      - a field of no fixed width
      - a run counted by a field
  *)

Module CurrenexForexNowV10.

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
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  Some ({| sequence_number := sequence_number_value; timestamp := timestamp_value; message_type := message_type_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module LogonMessage.

    (** Client initiates a session by submitting a Logon message to Currenex_NOW *)
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

  End LogonMessage.

  Module LogoutMessage.

    (** Terminate a session by sending or receiving a Logout message *)
    Record t := {
      user_id : list byte;
      session_id : N;
      reason_alpha_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 20 /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reason_alpha_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (user_id record) ++
      encode_uint 4 (session_id record) ++
      encode_bytes 3 (reason_alpha_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (reason_alpha_3_value, bytes) =>
                  Some ({| user_id := user_id_value; session_id := session_id_value; reason_alpha_3 := reason_alpha_3_value |}, bytes)
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

  End LogoutMessage.

  Module HeartBeatMessage.

    (** Keep-alive ping sent every 15 seconds; client must respond *)
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

  End HeartBeatMessage.

  Module InstrumentInfo.

    (** Definition of a currency or metal instrument *)
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

  Module InstrumentInfoAckMessage.

    (** Acknowledge receipt of InstrumentInfo *)
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

  End InstrumentInfoAckMessage.

  Module SubscriptionReplyMessage.

    (** Response to SubscriptionRequest *)
    Record t := {
      session_id : N;
      instrument_index : N;
      type : list byte;
      reason_alpha_50 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (type record) = 1 /\
      Datatypes.length (reason_alpha_50 record) = 50.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 2 (instrument_index record) ++
      encode_bytes 1 (type record) ++
      encode_bytes 50 (reason_alpha_50 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (instrument_index_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (type_value, bytes) =>
                  match decode_bytes 50 bytes with
                  | None => None
                  | Some (reason_alpha_50_value, bytes) =>
                      Some ({| session_id := session_id_value; instrument_index := instrument_index_value; type := type_value; reason_alpha_50 := reason_alpha_50_value |}, bytes)
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

  End SubscriptionReplyMessage.

  Module MassSubscriptionReplyMessage.

    (** Response to MassSubscriptionRequest *)
    Record t := {
      session_id : N;
      type : list byte;
      reason_alpha_50 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (type record) = 1 /\
      Datatypes.length (reason_alpha_50 record) = 50.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (type record) ++
      encode_bytes 50 (reason_alpha_50 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (type_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (reason_alpha_50_value, bytes) =>
                  Some ({| session_id := session_id_value; type := type_value; reason_alpha_50 := reason_alpha_50_value |}, bytes)
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

  End MassSubscriptionReplyMessage.

  Module Bid.

    (** Market level bid *)
    Record t := {
      rate : N;
      amount : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (rate record < 256 ^ N.of_nat 4)%N /\
      (amount record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (rate record) ++
      encode_uint 8 (amount record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (rate_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (amount_value, bytes) =>
              Some ({| rate := rate_value; amount := amount_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Bid.

  Module Offer.

    (** Market level offer *)
    Record t := {
      rate : N;
      amount : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (rate record < 256 ^ N.of_nat 4)%N /\
      (amount record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (rate record) ++
      encode_uint 8 (amount record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (rate_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (amount_value, bytes) =>
              Some ({| rate := rate_value; amount := amount_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Offer.

  Module PaidGivenMessage.

    (** Latest trade versus liquidity *)
    Record t := {
      instrument_index : N;
      rate : N;
      size_indicator : list byte;
      paid_given_indicator : list byte;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      (rate record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (size_indicator record) = 1 /\
      Datatypes.length (paid_given_indicator record) = 1 /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (instrument_index record) ++
      encode_uint 4 (rate record) ++
      encode_bytes 1 (size_indicator record) ++
      encode_bytes 1 (paid_given_indicator record) ++
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
              | Some (size_indicator_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (paid_given_indicator_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transact_time_value, bytes) =>
                          Some ({| instrument_index := instrument_index_value; rate := rate_value; size_indicator := size_indicator_value; paid_given_indicator := paid_given_indicator_value; transact_time := transact_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End PaidGivenMessage.

  Module ConfFactor75.

    (** 75th percentile confidence factor *)
    Record t := {
      bid_price : N;
      offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (offer_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (bid_price_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (offer_price_value, bytes) =>
              Some ({| bid_price := bid_price_value; offer_price := offer_price_value |}, bytes)
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

  End ConfFactor75.

  Module ConfFactor50.

    (** 50th percentile confidence factor *)
    Record t := {
      bid_price : N;
      offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (offer_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (bid_price_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (offer_price_value, bytes) =>
              Some ({| bid_price := bid_price_value; offer_price := offer_price_value |}, bytes)
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

  End ConfFactor50.

  Module ConfFactor25.

    (** 25th percentile confidence factor *)
    Record t := {
      bid_price : N;
      offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (offer_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (bid_price_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (offer_price_value, bytes) =>
              Some ({| bid_price := bid_price_value; offer_price := offer_price_value |}, bytes)
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

  End ConfFactor25.

  Module WamrWithConfidenceFactorMessage.

    (** Weighted average mid-rate with confidence factors *)
    Record t := {
      instrument_index : N;
      price : N;
      conf_factor_75 : ConfFactor75.t;
      conf_factor_50 : ConfFactor50.t;
      conf_factor_25 : ConfFactor25.t;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      ConfFactor75.bounded (conf_factor_75 record) /\
      ConfFactor50.bounded (conf_factor_50 record) /\
      ConfFactor25.bounded (conf_factor_25 record) /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (instrument_index record) ++
      encode_uint 4 (price record) ++
      ConfFactor75.encode (conf_factor_75 record) ++
      ConfFactor50.encode (conf_factor_50 record) ++
      ConfFactor25.encode (conf_factor_25 record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (instrument_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match ConfFactor75.decode bytes with
              | None => None
              | Some (conf_factor_75_value, bytes) =>
                  match ConfFactor50.decode bytes with
                  | None => None
                  | Some (conf_factor_50_value, bytes) =>
                      match ConfFactor25.decode bytes with
                      | None => None
                      | Some (conf_factor_25_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (timestamp_value, bytes) =>
                              Some ({| instrument_index := instrument_index_value; price := price_value; conf_factor_75 := conf_factor_75_value; conf_factor_50 := conf_factor_50_value; conf_factor_25 := conf_factor_25_value; timestamp := timestamp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ConfFactor75.encode_length, !ConfFactor50.encode_length, !ConfFactor25.encode_length. reflexivity.
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
      rewrite ConfFactor75.decode_encode by exact bound_2.
      rewrite ConfFactor50.decode_encode by exact bound_3.
      rewrite ConfFactor25.decode_encode by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ConfFactor75.eq_dec | apply ConfFactor50.eq_dec | apply ConfFactor25.eq_dec]. Defined.

  End WamrWithConfidenceFactorMessage.

  Module MidActivityIndicatorMessage.

    (** Indicator of mid-rate activity windows *)
    Record t := {
      instrument_index : N;
      activity_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (activity_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (instrument_index record) ++
      encode_bytes 1 (activity_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (instrument_index_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (activity_indicator_value, bytes) =>
              Some ({| instrument_index := instrument_index_value; activity_indicator := activity_indicator_value |}, bytes)
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

  End MidActivityIndicatorMessage.

  Module RejectMessage.

    (** Reject incorrectly formatted or invalid messages *)
    Record t := {
      session_id : N;
      reject_msg_type : list byte;
      reason_alpha_50 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reject_msg_type record) = 1 /\
      Datatypes.length (reason_alpha_50 record) = 50.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (reject_msg_type record) ++
      encode_bytes 50 (reason_alpha_50 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reject_msg_type_value, bytes) =>
              match decode_bytes 50 bytes with
              | None => None
              | Some (reason_alpha_50_value, bytes) =>
                  Some ({| session_id := session_id_value; reject_msg_type := reject_msg_type_value; reason_alpha_50 := reason_alpha_50_value |}, bytes)
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

End CurrenexForexNowV10.
