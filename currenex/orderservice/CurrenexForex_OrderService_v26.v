From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Currenex Order Service

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

Module CurrenexForexOrderServiceV26.

  Module MessageHeader.

    (** Currenex Market Data Message Header *)
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

    (** Client initiates a session by submitting a Logon message *)
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

    (** Terminate a session by sending a Logout message *)
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

    (** Keep-alive ping sent every three seconds; client must respond *)
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

  Module InstrumentInfoRequest.

    (** Request list of supported instruments *)
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

  End InstrumentInfoRequest.

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

  Module NewOrderRequest.

    (** Submit a new order request *)
    Record t := {
      cl_order_id : N;
      order_type : list byte;
      instrument_index : N;
      side : list byte;
      order_amt : N;
      min_amt : N;
      price : N;
      show_amt : N;
      expire_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_type record) = 1 /\
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (order_amt record < 256 ^ N.of_nat 8)%N /\
      (min_amt record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (show_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (expire_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (cl_order_id record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 2 (instrument_index record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_amt record) ++
      encode_uint 8 (min_amt record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (show_amt record) ++
      encode_bytes 1 (expire_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (cl_order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (order_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (instrument_index_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_amt_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (min_amt_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (show_amt_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (expire_type_value, bytes) =>
                                          Some ({| cl_order_id := cl_order_id_value; order_type := order_type_value; instrument_index := instrument_index_value; side := side_value; order_amt := order_amt_value; min_amt := min_amt_value; price := price_value; show_amt := show_amt_value; expire_type := expire_type_value |}, bytes)
                                      end
                                  end
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderRequest.

  Module NewOrderAck.

    (** Acknowledge new order *)
    Record t := {
      cl_order_id : N;
      order_id : N;
      ack_status : list byte;
      error_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ack_status record) = 1 /\
      (error_code record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (cl_order_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (ack_status record) ++
      encode_uint 2 (error_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (cl_order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (ack_status_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (error_code_value, bytes) =>
                      Some ({| cl_order_id := cl_order_id_value; order_id := order_id_value; ack_status := ack_status_value; error_code := error_code_value |}, bytes)
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

  End NewOrderAck.

  Module OrderCancelRequest.

    (** Request cancellation of an order *)
    Record t := {
      new_cl_order_id : N;
      prev_cl_order_id : N;
      instrument_index : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (prev_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (instrument_index record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_cl_order_id record) ++
      encode_uint 4 (prev_cl_order_id record) ++
      encode_uint 2 (instrument_index record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_cl_order_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (prev_cl_order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (instrument_index_value, bytes) =>
                  Some ({| new_cl_order_id := new_cl_order_id_value; prev_cl_order_id := prev_cl_order_id_value; instrument_index := instrument_index_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End OrderCancelRequest.

  Module OrderCancelReject.

    (** Rejection of Order Cancel Request *)
    Record t := {
      new_cl_order_id : N;
      prev_cl_order_id : N;
      error_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (prev_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_cl_order_id record) ++
      encode_uint 4 (prev_cl_order_id record) ++
      encode_uint 2 (error_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_cl_order_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (prev_cl_order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (error_code_value, bytes) =>
                  Some ({| new_cl_order_id := new_cl_order_id_value; prev_cl_order_id := prev_cl_order_id_value; error_code := error_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End OrderCancelReject.

  Module OrderReplaceOrCancelRequest.

    (** Replace or cancel an order *)
    Record t := {
      new_cl_order_id : N;
      orig_cl_order_id : N;
      order_amt : N;
      price : N;
      instrument_index : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (orig_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (order_amt record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (instrument_index record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_cl_order_id record) ++
      encode_uint 4 (orig_cl_order_id record) ++
      encode_uint 8 (order_amt record) ++
      encode_uint 4 (price record) ++
      encode_uint 2 (instrument_index record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_cl_order_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orig_cl_order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_amt_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (instrument_index_value, bytes) =>
                          Some ({| new_cl_order_id := new_cl_order_id_value; orig_cl_order_id := orig_cl_order_id_value; order_amt := order_amt_value; price := price_value; instrument_index := instrument_index_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderReplaceOrCancelRequest.

  Module OrderReplaceOrCancelAck.

    (** Acknowledge replace/cancel *)
    Record t := {
      new_cl_order_id : N;
      prev_cl_order_id : N;
      status : list byte;
      error_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (prev_cl_order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (status record) = 1 /\
      (error_code record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_cl_order_id record) ++
      encode_uint 4 (prev_cl_order_id record) ++
      encode_bytes 1 (status record) ++
      encode_uint 2 (error_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_cl_order_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (prev_cl_order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (error_code_value, bytes) =>
                      Some ({| new_cl_order_id := new_cl_order_id_value; prev_cl_order_id := prev_cl_order_id_value; status := status_value; error_code := error_code_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderReplaceOrCancelAck.

  Module OrderCanceledOrExpired.

    (** Unsolicited cancellation/expiry notice *)
    Record t := {
      cl_order_id : N;
      order_id : N;
      status : list byte;
      type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (status record) = 1 /\
      (type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (cl_order_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (status record) ++
      encode_uint 2 (type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (cl_order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (type_value, bytes) =>
                      Some ({| cl_order_id := cl_order_id_value; order_id := order_id_value; status := status_value; type := type_value |}, bytes)
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

  End OrderCanceledOrExpired.

  Module Trade.

    (** Trade execution notification *)
    Record t := {
      cl_order_id : N;
      order_id : N;
      instrument_index : N;
      side : list byte;
      fill_amt : N;
      fill_rate : N;
      exec_broker : list byte;
      execution_id : list byte;
      exec_type : list byte;
      settle_date : N;
      trade_date : N;
      transact_time : N;
      leaves_amt : N;
      aggressor_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_index record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (fill_amt record < 256 ^ N.of_nat 8)%N /\
      (fill_rate record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exec_broker record) = 4 /\
      Datatypes.length (execution_id record) = 20 /\
      Datatypes.length (exec_type record) = 1 /\
      (settle_date record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (leaves_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (aggressor_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (cl_order_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (instrument_index record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (fill_amt record) ++
      encode_uint 4 (fill_rate record) ++
      encode_bytes 4 (exec_broker record) ++
      encode_bytes 20 (execution_id record) ++
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (settle_date record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (leaves_amt record) ++
      encode_bytes 1 (aggressor_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (cl_order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (instrument_index_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (fill_amt_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (fill_rate_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (exec_broker_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (execution_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (exec_type_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (settle_date_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (trade_date_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (transact_time_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (leaves_amt_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (aggressor_flag_value, bytes) =>
                                                              Some ({| cl_order_id := cl_order_id_value; order_id := order_id_value; instrument_index := instrument_index_value; side := side_value; fill_amt := fill_amt_value; fill_rate := fill_rate_value; exec_broker := exec_broker_value; execution_id := execution_id_value; exec_type := exec_type_value; settle_date := settle_date_value; trade_date := trade_date_value; transact_time := transact_time_value; leaves_amt := leaves_amt_value; aggressor_flag := aggressor_flag_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 85.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Trade.

  Module PendingFill.

    (** Notification of expected fill *)
    Record t := {
      cl_order_id : N;
      order_id : N;
      trade_link_id : N;
      fill_amt : N;
      fill_rate : N;
      aggressor_flag : list byte;
      exec_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trade_link_id record < 256 ^ N.of_nat 4)%N /\
      (fill_amt record < 256 ^ N.of_nat 8)%N /\
      (fill_rate record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (aggressor_flag record) = 1 /\
      Datatypes.length (exec_broker record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (cl_order_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (trade_link_id record) ++
      encode_uint 8 (fill_amt record) ++
      encode_uint 4 (fill_rate record) ++
      encode_bytes 1 (aggressor_flag record) ++
      encode_bytes 4 (exec_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (cl_order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_link_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (fill_amt_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (fill_rate_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (aggressor_flag_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (exec_broker_value, bytes) =>
                                  Some ({| cl_order_id := cl_order_id_value; order_id := order_id_value; trade_link_id := trade_link_id_value; fill_amt := fill_amt_value; fill_rate := fill_rate_value; aggressor_flag := aggressor_flag_value; exec_broker := exec_broker_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PendingFill.

  Module PendingFillCancel.

    (** Notification of pending fill cancellation *)
    Record t := {
      cl_order_id : N;
      order_id : N;
      trade_link_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_order_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trade_link_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (cl_order_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (trade_link_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (cl_order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_link_id_value, bytes) =>
                  Some ({| cl_order_id := cl_order_id_value; order_id := order_id_value; trade_link_id := trade_link_id_value |}, bytes)
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

  End PendingFillCancel.

  Module TradePending.

    (** Trade notification linked to pending fill *)
    Record t := {
      exec_type : list byte;
      settle_date : N;
      trade_date : N;
      transact_time : N;
      leaves_amt : N;
      aggressor_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exec_type record) = 1 /\
      (settle_date record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (leaves_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (aggressor_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exec_type record) ++
      encode_uint 8 (settle_date record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (leaves_amt record) ++
      encode_bytes 1 (aggressor_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exec_type_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (settle_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trade_date_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transact_time_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (leaves_amt_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (aggressor_flag_value, bytes) =>
                              Some ({| exec_type := exec_type_value; settle_date := settle_date_value; trade_date := trade_date_value; transact_time := transact_time_value; leaves_amt := leaves_amt_value; aggressor_flag := aggressor_flag_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradePending.

  Module ResendRequest.

    (** Request retransmission of missed messages *)
    Record t := {
      begin_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_no_value, bytes) =>
          Some ({| begin_seq_no := begin_seq_no_value |}, bytes)
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

  End ResendRequest.

  Module GapFill.

    (** Skip non-resendable or unavailable messages *)
    Record t := {
      new_seq_no : N;
      reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_seq_no record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_seq_no record) ++
      encode_bytes 1 (reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_seq_no_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reason_code_value, bytes) =>
              Some ({| new_seq_no := new_seq_no_value; reason_code := reason_code_value |}, bytes)
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

  End GapFill.

End CurrenexForexOrderServiceV26.
