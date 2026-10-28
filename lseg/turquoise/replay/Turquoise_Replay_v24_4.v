From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * London Stock Exchange Replay

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
      - a run counted by a field
      - a field read in bits
  *)

Module TurquoiseReplayV244.

  Module UnitHeader.

    (** Gtp Tcp Unit Header *)
    Record t := {
      length_ : N;
      message_count : N;
      market_data_group : list byte;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_data_group record) = 1 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_bytes 1 (market_data_group record) ++
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; market_data_group := market_data_group_value; sequence_number := sequence_number_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnitHeader.

  Module MessageHeader.

    (** Gtp Tcp Message Header *)
    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module LoginRequestMessage.

    (** Used by the client to log in to the replay or recovery channel. *)
    Record t := {
      username : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (username record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (username_value, bytes) =>
          Some ({| username := username_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End LoginRequestMessage.

  Module ReplayRequestMessage.

    (** Used by the client to request a retransmission of messages on the replay channel. *)
    Record t := {
      first_message : N;
      count : N;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (first_message record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 4)%N /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (first_message record) ++
      encode_uint 4 (count record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (first_message_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (count_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (request_id_value, bytes) =>
                  Some ({| first_message := first_message_value; count := count_value; request_id := request_id_value |}, bytes)
              end
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

  End ReplayRequestMessage.

  Module LoginResponseMessage.

    (** Used by the server to accept or reject a login request to the replay or recovery channel. *)
    Record t := {
      login_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_status_value, bytes) =>
          Some ({| login_status := login_status_value |}, bytes)
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

  End LoginResponseMessage.

  Module ReplayResponseMessage.

    (** Used by the server to respond to a retransmission request on the replay channel. *)
    Record t := {
      first_message : N;
      count : N;
      replay_status : list byte;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (first_message record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (replay_status record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (first_message record) ++
      encode_uint 4 (count record) ++
      encode_bytes 1 (replay_status record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (first_message_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (replay_status_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (request_id_value, bytes) =>
                      Some ({| first_message := first_message_value; count := count_value; replay_status := replay_status_value; request_id := request_id_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplayResponseMessage.

  Module ReplayAndRecoveryCompleteMessage.

    (** Used by the server to indicate the successful completion of servicing a message replay or a recovery request. *)
    Record t := {
      request_id : N;
      trading_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_bytes 1 (trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_status_value, bytes) =>
              Some ({| request_id := request_id_value; trading_status := trading_status_value |}, bytes)
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

  End ReplayAndRecoveryCompleteMessage.

  Module SystemEventMessage.

    (** Sent to indicate the start and end of the day. *)
    Record t := {
      timestamp : N;
      event_code : list byte;
      source_venue : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1 /\
      (source_venue record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 2 (source_venue record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  Some ({| timestamp := timestamp_value; event_code := event_code_value; source_venue := source_venue_value |}, bytes)
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

  End SystemEventMessage.

  Module InstrumentStatusMessage.

    (** Used to communicate scheduled and unscheduled session changes *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      trading_status : list byte;
      session_change_reason : N;
      new_end_time : list byte;
      order_book_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (session_change_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (new_end_time record) = 6 /\
      (order_book_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint 1 (session_change_reason record) ++
      encode_bytes 6 (new_end_time record) ++
      encode_uint 1 (order_book_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (session_change_reason_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (new_end_time_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_book_type_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; trading_status := trading_status_value; session_change_reason := session_change_reason_value; new_end_time := new_end_time_value; order_book_type := order_book_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentStatusMessage.

  Module AddOrderIncrementalMessage.

    (** Sent to instruct recipients to add a new displayable order to the retrospective order book *)
    Record t := {
      timestamp : N;
      order_id : N;
      side : list byte;
      size : N;
      instrument : N;
      price : N;
      transaction_time : N;
      source_venue : N;
      order_book_type : N;
      participant : list byte;
      order_type : N;
      rfq_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (size record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (order_book_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (participant record) = 11 /\
      (order_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (rfq_id record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (size record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (transaction_time record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 1 (order_book_type record) ++
      encode_bytes 11 (participant record) ++
      encode_uint 1 (order_type record) ++
      encode_bytes 10 (rfq_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (size_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (instrument_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transaction_time_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (source_venue_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_book_type_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (participant_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (order_type_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (rfq_id_value, bytes) =>
                                                      Some ({| timestamp := timestamp_value; order_id := order_id_value; side := side_value; size := size_value; instrument := instrument_value; price := price_value; transaction_time := transaction_time_value; source_venue := source_venue_value; order_book_type := order_book_type_value; participant := participant_value; order_type := order_type_value; rfq_id := rfq_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderIncrementalMessage.

  Module OrderDeleteMessage.

    (** Sent to instruct recipients to delete an order from the retrospective order book *)
    Record t := {
      timestamp : N;
      order_id : N;
      instrument : N;
      side : list byte;
      order_book_type : N;
      source_venue : N;
      previous_price : N;
      previous_quantity : N;
      transaction_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (order_book_type record < 256 ^ N.of_nat 1)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (previous_price record < 256 ^ N.of_nat 8)%N /\
      (previous_quantity record < 256 ^ N.of_nat 8)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (instrument record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (order_book_type record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (previous_price record) ++
      encode_uint 8 (previous_quantity record) ++
      encode_uint 8 (transaction_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (order_book_type_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (source_venue_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (previous_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (previous_quantity_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (transaction_time_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; order_id := order_id_value; instrument := instrument_value; side := side_value; order_book_type := order_book_type_value; source_venue := source_venue_value; previous_price := previous_price_value; previous_quantity := previous_quantity_value; transaction_time := transaction_time_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderDeleteMessage.

  Module OrderBookClearMessage.

    (** Sent to instruct recipients to remove all orders from the order book for the specified instrument *)
    Record t := {
      timestamp : N;
      source_venue : N;
      instrument : N;
      order_book_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (order_book_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 1 (order_book_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (source_venue_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (order_book_type_value, bytes) =>
                      Some ({| timestamp := timestamp_value; source_venue := source_venue_value; instrument := instrument_value; order_book_type := order_book_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderBookClearMessage.

  Module StatisticsMessage.

    (** Contains a set of statistics that are updated frequently, usually as a result of executions *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      volume : N;
      volume_on_book_only : N;
      vwap : N;
      vwap_on_book_only : N;
      number_of_trades : N;
      number_of_trades_on_book_only : N;
      turnover : N;
      turnover_on_book_only : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (volume_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (vwap_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (number_of_trades record < 256 ^ N.of_nat 4)%N /\
      (number_of_trades_on_book_only record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (turnover_on_book_only record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (volume record) ++
      encode_uint 8 (volume_on_book_only record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (vwap_on_book_only record) ++
      encode_uint 4 (number_of_trades record) ++
      encode_uint 4 (number_of_trades_on_book_only record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 8 (turnover_on_book_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (volume_on_book_only_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (vwap_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (vwap_on_book_only_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (number_of_trades_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (number_of_trades_on_book_only_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (turnover_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (turnover_on_book_only_value, bytes) =>
                                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; volume := volume_value; volume_on_book_only := volume_on_book_only_value; vwap := vwap_value; vwap_on_book_only := vwap_on_book_only_value; number_of_trades := number_of_trades_value; number_of_trades_on_book_only := number_of_trades_on_book_only_value; turnover := turnover_value; turnover_on_book_only := turnover_on_book_only_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StatisticsMessage.

  Module StatisticsUpdateMessage.

    (** Contains a set of statistics that are not updated frequently *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      statistic_type : N;
      statistic_price : N;
      statistic_size : N;
      auction_type : list byte;
      imbalance_quantity : N;
      auction_info : list byte;
      opening_closing_price_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (statistic_type record < 256 ^ N.of_nat 2)%N /\
      (statistic_price record < 256 ^ N.of_nat 8)%N /\
      (statistic_size record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (imbalance_quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_info record) = 1 /\
      Datatypes.length (opening_closing_price_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 2 (statistic_type record) ++
      encode_uint 8 (statistic_price record) ++
      encode_uint 8 (statistic_size record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (imbalance_quantity record) ++
      encode_bytes 1 (auction_info record) ++
      encode_bytes 1 (opening_closing_price_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (statistic_type_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (statistic_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (statistic_size_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (auction_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (imbalance_quantity_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (auction_info_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (opening_closing_price_indicator_value, bytes) =>
                                              Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; statistic_type := statistic_type_value; statistic_price := statistic_price_value; statistic_size := statistic_size_value; auction_type := auction_type_value; imbalance_quantity := imbalance_quantity_value; auction_info := auction_info_value; opening_closing_price_indicator := opening_closing_price_indicator_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticsUpdateMessage.

  Module MifidIiTradeMessage.

    (** Sent to represent different types of MiFID compliant trades published by markets *)
    Record t := {
      timestamp : N;
      source_venue : N;
      instrument : N;
      transaction_identification_code : list byte;
      trade_type : N;
      auction_type : list byte;
      mi_fid_price : list byte;
      mi_fid_quantity : list byte;
      trading_date_and_time : list byte;
      instrument_identification_code_type : list byte;
      instrument_identification_code : list byte;
      price_notation : list byte;
      price_major_currency : list byte;
      notional_amount : list byte;
      notional_currency : list byte;
      venue_of_execution : list byte;
      publication_date_and_time : list byte;
      pt_ref_price_waiver_flag : list byte;
      reserved_4 : N;
      market_closing_price_flag : list byte;
      pt_algo_trade : list byte;
      pt_cancellation_flag : list byte;
      pt_amendment_flag : list byte;
      reserved_1 : N;
      reserved_3 : N;
      reserved_20 : list byte;
      second_reserved_4 : N;
      trade_qualifier : list byte;
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      negotiation_indicator : list byte;
      agency_cross_indicator : list byte;
      modification_indicator : list byte;
      reference_price_indicator : list byte;
      special_dividend_indicator : list byte;
      off_book_automated_indicator : list byte;
      price_formation_indicator : list byte;
      algorithmic_indicator : list byte;
      post_trade_deferral_reason : list byte;
      deferral_enrichment_type : list byte;
      duplicative_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (transaction_identification_code record) = 52 /\
      (trade_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (mi_fid_price record) = 20 /\
      Datatypes.length (mi_fid_quantity record) = 20 /\
      Datatypes.length (trading_date_and_time record) = 27 /\
      Datatypes.length (instrument_identification_code_type record) = 4 /\
      Datatypes.length (instrument_identification_code record) = 12 /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (price_major_currency record) = 3 /\
      Datatypes.length (notional_amount record) = 20 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (venue_of_execution record) = 4 /\
      Datatypes.length (publication_date_and_time record) = 27 /\
      Datatypes.length (pt_ref_price_waiver_flag record) = 4 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_closing_price_flag record) = 4 /\
      Datatypes.length (pt_algo_trade record) = 4 /\
      Datatypes.length (pt_cancellation_flag record) = 4 /\
      Datatypes.length (pt_amendment_flag record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N /\
      Datatypes.length (reserved_20 record) = 20 /\
      (second_reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_qualifier record) = 1 /\
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (negotiation_indicator record) = 1 /\
      Datatypes.length (agency_cross_indicator record) = 1 /\
      Datatypes.length (modification_indicator record) = 1 /\
      Datatypes.length (reference_price_indicator record) = 1 /\
      Datatypes.length (special_dividend_indicator record) = 1 /\
      Datatypes.length (off_book_automated_indicator record) = 1 /\
      Datatypes.length (price_formation_indicator record) = 1 /\
      Datatypes.length (algorithmic_indicator record) = 1 /\
      Datatypes.length (post_trade_deferral_reason record) = 1 /\
      Datatypes.length (deferral_enrichment_type record) = 1 /\
      Datatypes.length (duplicative_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (instrument record) ++
      encode_bytes 52 (transaction_identification_code record) ++
      encode_uint 1 (trade_type record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 20 (mi_fid_price record) ++
      encode_bytes 20 (mi_fid_quantity record) ++
      encode_bytes 27 (trading_date_and_time record) ++
      encode_bytes 4 (instrument_identification_code_type record) ++
      encode_bytes 12 (instrument_identification_code record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 3 (price_major_currency record) ++
      encode_bytes 20 (notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_bytes 27 (publication_date_and_time record) ++
      encode_bytes 4 (pt_ref_price_waiver_flag record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_bytes 4 (market_closing_price_flag record) ++
      encode_bytes 4 (pt_algo_trade record) ++
      encode_bytes 4 (pt_cancellation_flag record) ++
      encode_bytes 4 (pt_amendment_flag record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 3 (reserved_3 record) ++
      encode_bytes 20 (reserved_20 record) ++
      encode_uint 4 (second_reserved_4 record) ++
      encode_bytes 1 (trade_qualifier record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (negotiation_indicator record) ++
      encode_bytes 1 (agency_cross_indicator record) ++
      encode_bytes 1 (modification_indicator record) ++
      encode_bytes 1 (reference_price_indicator record) ++
      encode_bytes 1 (special_dividend_indicator record) ++
      encode_bytes 1 (off_book_automated_indicator record) ++
      encode_bytes 1 (price_formation_indicator record) ++
      encode_bytes 1 (algorithmic_indicator record) ++
      encode_bytes 1 (post_trade_deferral_reason record) ++
      encode_bytes 1 (deferral_enrichment_type record) ++
      encode_bytes 1 (duplicative_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (source_venue_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 52 bytes with
                  | None => None
                  | Some (transaction_identification_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trade_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (auction_type_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (mi_fid_price_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (mi_fid_quantity_value, bytes) =>
                                      match decode_bytes 27 bytes with
                                      | None => None
                                      | Some (trading_date_and_time_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (instrument_identification_code_type_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (instrument_identification_code_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (price_notation_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (price_major_currency_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (notional_amount_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (notional_currency_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (venue_of_execution_value, bytes) =>
                                                                      match decode_bytes 27 bytes with
                                                                      | None => None
                                                                      | Some (publication_date_and_time_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (pt_ref_price_waiver_flag_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (reserved_4_value, bytes) =>
                                                                                  match decode_bytes 4 bytes with
                                                                                  | None => None
                                                                                  | Some (market_closing_price_flag_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (pt_algo_trade_value, bytes) =>
                                                                                          match decode_bytes 4 bytes with
                                                                                          | None => None
                                                                                          | Some (pt_cancellation_flag_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (pt_amendment_flag_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (reserved_1_value, bytes) =>
                                                                                                      match decode_uint 3 bytes with
                                                                                                      | None => None
                                                                                                      | Some (reserved_3_value, bytes) =>
                                                                                                          match decode_bytes 20 bytes with
                                                                                                          | None => None
                                                                                                          | Some (reserved_20_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (second_reserved_4_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (trade_qualifier_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (market_mechanism_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (trading_mode_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (transaction_category_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (negotiation_indicator_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (agency_cross_indicator_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (modification_indicator_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (reference_price_indicator_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (special_dividend_indicator_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (off_book_automated_indicator_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (price_formation_indicator_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (algorithmic_indicator_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (post_trade_deferral_reason_value, bytes) =>
                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (deferral_enrichment_type_value, bytes) =>
                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (duplicative_indicator_value, bytes) =>
                                                                                                                                                                              Some ({| timestamp := timestamp_value; source_venue := source_venue_value; instrument := instrument_value; transaction_identification_code := transaction_identification_code_value; trade_type := trade_type_value; auction_type := auction_type_value; mi_fid_price := mi_fid_price_value; mi_fid_quantity := mi_fid_quantity_value; trading_date_and_time := trading_date_and_time_value; instrument_identification_code_type := instrument_identification_code_type_value; instrument_identification_code := instrument_identification_code_value; price_notation := price_notation_value; price_major_currency := price_major_currency_value; notional_amount := notional_amount_value; notional_currency := notional_currency_value; venue_of_execution := venue_of_execution_value; publication_date_and_time := publication_date_and_time_value; pt_ref_price_waiver_flag := pt_ref_price_waiver_flag_value; reserved_4 := reserved_4_value; market_closing_price_flag := market_closing_price_flag_value; pt_algo_trade := pt_algo_trade_value; pt_cancellation_flag := pt_cancellation_flag_value; pt_amendment_flag := pt_amendment_flag_value; reserved_1 := reserved_1_value; reserved_3 := reserved_3_value; reserved_20 := reserved_20_value; second_reserved_4 := second_reserved_4_value; trade_qualifier := trade_qualifier_value; market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; negotiation_indicator := negotiation_indicator_value; agency_cross_indicator := agency_cross_indicator_value; modification_indicator := modification_indicator_value; reference_price_indicator := reference_price_indicator_value; special_dividend_indicator := special_dividend_indicator_value; off_book_automated_indicator := off_book_automated_indicator_value; price_formation_indicator := price_formation_indicator_value; algorithmic_indicator := algorithmic_indicator_value; post_trade_deferral_reason := post_trade_deferral_reason_value; deferral_enrichment_type := deferral_enrichment_type_value; duplicative_indicator := duplicative_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 283.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 bound_41]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MifidIiTradeMessage.

  Module MiFidIiTradeCrossMessage.

    (** Sent to indicate a MiFID compliant cross trade *)
    Record t := {
      timestamp : N;
      source_venue : N;
      instrument : N;
      transaction_identification_code : list byte;
      cross_id : list byte;
      cross_type : N;
      mi_fid_price : list byte;
      mi_fid_quantity : list byte;
      trading_date_and_time : list byte;
      instrument_identification_code_type : list byte;
      instrument_identification_code : list byte;
      price_notation : list byte;
      price_major_currency : list byte;
      notional_amount : list byte;
      notional_currency : list byte;
      venue_of_execution : list byte;
      publication_date_and_time : list byte;
      reserved_4 : N;
      nt_pre_trade_waiver_flag : list byte;
      pt_algo_trade : list byte;
      second_reserved_4 : N;
      pt_cancellation_flag : list byte;
      pt_amendment_flag : list byte;
      reserved_1 : N;
      reserved_3 : N;
      reserved_20 : list byte;
      third_reserved_4 : N;
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      negotiation_indicator : list byte;
      agency_cross_indicator : list byte;
      modification_indicator : list byte;
      reference_price_indicator : list byte;
      special_dividend_indicator : list byte;
      off_book_automated_indicator : list byte;
      price_formation_indicator : list byte;
      algorithmic_indicator : list byte;
      post_trade_deferral_reason : list byte;
      deferral_enrichment_type : list byte;
      duplicative_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (transaction_identification_code record) = 52 /\
      Datatypes.length (cross_id record) = 20 /\
      (cross_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (mi_fid_price record) = 20 /\
      Datatypes.length (mi_fid_quantity record) = 20 /\
      Datatypes.length (trading_date_and_time record) = 27 /\
      Datatypes.length (instrument_identification_code_type record) = 4 /\
      Datatypes.length (instrument_identification_code record) = 12 /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (price_major_currency record) = 3 /\
      Datatypes.length (notional_amount record) = 20 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (venue_of_execution record) = 4 /\
      Datatypes.length (publication_date_and_time record) = 27 /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (nt_pre_trade_waiver_flag record) = 4 /\
      Datatypes.length (pt_algo_trade record) = 4 /\
      (second_reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (pt_cancellation_flag record) = 4 /\
      Datatypes.length (pt_amendment_flag record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N /\
      Datatypes.length (reserved_20 record) = 20 /\
      (third_reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (negotiation_indicator record) = 1 /\
      Datatypes.length (agency_cross_indicator record) = 1 /\
      Datatypes.length (modification_indicator record) = 1 /\
      Datatypes.length (reference_price_indicator record) = 1 /\
      Datatypes.length (special_dividend_indicator record) = 1 /\
      Datatypes.length (off_book_automated_indicator record) = 1 /\
      Datatypes.length (price_formation_indicator record) = 1 /\
      Datatypes.length (algorithmic_indicator record) = 1 /\
      Datatypes.length (post_trade_deferral_reason record) = 1 /\
      Datatypes.length (deferral_enrichment_type record) = 1 /\
      Datatypes.length (duplicative_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (instrument record) ++
      encode_bytes 52 (transaction_identification_code record) ++
      encode_bytes 20 (cross_id record) ++
      encode_uint 1 (cross_type record) ++
      encode_bytes 20 (mi_fid_price record) ++
      encode_bytes 20 (mi_fid_quantity record) ++
      encode_bytes 27 (trading_date_and_time record) ++
      encode_bytes 4 (instrument_identification_code_type record) ++
      encode_bytes 12 (instrument_identification_code record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 3 (price_major_currency record) ++
      encode_bytes 20 (notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_bytes 27 (publication_date_and_time record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_bytes 4 (nt_pre_trade_waiver_flag record) ++
      encode_bytes 4 (pt_algo_trade record) ++
      encode_uint 4 (second_reserved_4 record) ++
      encode_bytes 4 (pt_cancellation_flag record) ++
      encode_bytes 4 (pt_amendment_flag record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 3 (reserved_3 record) ++
      encode_bytes 20 (reserved_20 record) ++
      encode_uint 4 (third_reserved_4 record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (negotiation_indicator record) ++
      encode_bytes 1 (agency_cross_indicator record) ++
      encode_bytes 1 (modification_indicator record) ++
      encode_bytes 1 (reference_price_indicator record) ++
      encode_bytes 1 (special_dividend_indicator record) ++
      encode_bytes 1 (off_book_automated_indicator record) ++
      encode_bytes 1 (price_formation_indicator record) ++
      encode_bytes 1 (algorithmic_indicator record) ++
      encode_bytes 1 (post_trade_deferral_reason record) ++
      encode_bytes 1 (deferral_enrichment_type record) ++
      encode_bytes 1 (duplicative_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (source_venue_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 52 bytes with
                  | None => None
                  | Some (transaction_identification_code_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (cross_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (cross_type_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (mi_fid_price_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (mi_fid_quantity_value, bytes) =>
                                      match decode_bytes 27 bytes with
                                      | None => None
                                      | Some (trading_date_and_time_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (instrument_identification_code_type_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (instrument_identification_code_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (price_notation_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (price_major_currency_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (notional_amount_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (notional_currency_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (venue_of_execution_value, bytes) =>
                                                                      match decode_bytes 27 bytes with
                                                                      | None => None
                                                                      | Some (publication_date_and_time_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (reserved_4_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (nt_pre_trade_waiver_flag_value, bytes) =>
                                                                                  match decode_bytes 4 bytes with
                                                                                  | None => None
                                                                                  | Some (pt_algo_trade_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (second_reserved_4_value, bytes) =>
                                                                                          match decode_bytes 4 bytes with
                                                                                          | None => None
                                                                                          | Some (pt_cancellation_flag_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (pt_amendment_flag_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (reserved_1_value, bytes) =>
                                                                                                      match decode_uint 3 bytes with
                                                                                                      | None => None
                                                                                                      | Some (reserved_3_value, bytes) =>
                                                                                                          match decode_bytes 20 bytes with
                                                                                                          | None => None
                                                                                                          | Some (reserved_20_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (third_reserved_4_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (market_mechanism_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (trading_mode_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (transaction_category_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (negotiation_indicator_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (agency_cross_indicator_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (modification_indicator_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (reference_price_indicator_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (special_dividend_indicator_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (off_book_automated_indicator_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (price_formation_indicator_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (algorithmic_indicator_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (post_trade_deferral_reason_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (deferral_enrichment_type_value, bytes) =>
                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (duplicative_indicator_value, bytes) =>
                                                                                                                                                                          Some ({| timestamp := timestamp_value; source_venue := source_venue_value; instrument := instrument_value; transaction_identification_code := transaction_identification_code_value; cross_id := cross_id_value; cross_type := cross_type_value; mi_fid_price := mi_fid_price_value; mi_fid_quantity := mi_fid_quantity_value; trading_date_and_time := trading_date_and_time_value; instrument_identification_code_type := instrument_identification_code_type_value; instrument_identification_code := instrument_identification_code_value; price_notation := price_notation_value; price_major_currency := price_major_currency_value; notional_amount := notional_amount_value; notional_currency := notional_currency_value; venue_of_execution := venue_of_execution_value; publication_date_and_time := publication_date_and_time_value; reserved_4 := reserved_4_value; nt_pre_trade_waiver_flag := nt_pre_trade_waiver_flag_value; pt_algo_trade := pt_algo_trade_value; second_reserved_4 := second_reserved_4_value; pt_cancellation_flag := pt_cancellation_flag_value; pt_amendment_flag := pt_amendment_flag_value; reserved_1 := reserved_1_value; reserved_3 := reserved_3_value; reserved_20 := reserved_20_value; third_reserved_4 := third_reserved_4_value; market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; negotiation_indicator := negotiation_indicator_value; agency_cross_indicator := agency_cross_indicator_value; modification_indicator := modification_indicator_value; reference_price_indicator := reference_price_indicator_value; special_dividend_indicator := special_dividend_indicator_value; off_book_automated_indicator := off_book_automated_indicator_value; price_formation_indicator := price_formation_indicator_value; algorithmic_indicator := algorithmic_indicator_value; post_trade_deferral_reason := post_trade_deferral_reason_value; deferral_enrichment_type := deferral_enrichment_type_value; duplicative_indicator := duplicative_indicator_value |}, bytes)
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
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 301.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 bound_40]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MiFidIiTradeCrossMessage.

  Module TradeSummaryMessage.

    (** Trade Summary message is used to disseminate results of multi and single fill trade events *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      transaction_time : N;
      far_price : N;
      total_executed_quantity : N;
      total_hidden_executed_quantity : N;
      deleted_order_quantity : N;
      side : list byte;
      best_bid_size : N;
      best_bid_price : N;
      best_offer_size : N;
      best_offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      (far_price record < 256 ^ N.of_nat 8)%N /\
      (total_executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (total_hidden_executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (deleted_order_quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (best_bid_size record < 256 ^ N.of_nat 8)%N /\
      (best_bid_price record < 256 ^ N.of_nat 8)%N /\
      (best_offer_size record < 256 ^ N.of_nat 8)%N /\
      (best_offer_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (transaction_time record) ++
      encode_uint 8 (far_price record) ++
      encode_uint 8 (total_executed_quantity record) ++
      encode_uint 8 (total_hidden_executed_quantity record) ++
      encode_uint 8 (deleted_order_quantity record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (best_bid_size record) ++
      encode_uint 8 (best_bid_price record) ++
      encode_uint 8 (best_offer_size record) ++
      encode_uint 8 (best_offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transaction_time_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (far_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (total_executed_quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (total_hidden_executed_quantity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (deleted_order_quantity_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (side_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (best_bid_size_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (best_bid_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (best_offer_size_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (best_offer_price_value, bytes) =>
                                                          Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; transaction_time := transaction_time_value; far_price := far_price_value; total_executed_quantity := total_executed_quantity_value; total_hidden_executed_quantity := total_hidden_executed_quantity_value; deleted_order_quantity := deleted_order_quantity_value; side := side_value; best_bid_size := best_bid_size_value; best_bid_price := best_bid_price_value; best_offer_size := best_offer_size_value; best_offer_price := best_offer_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 91.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
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

  End TradeSummaryMessage.

  Module AnalyticsMessage.

    (** Used to disseminate additional statistics including order book activity statistics *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      start_time : N;
      end_time : N;
      buy_order_count : N;
      sell_order_count : N;
      buy_order_size : N;
      sell_order_size : N;
      buy_order_cancellations : N;
      sell_order_cancellations : N;
      buy_limit_order_cancellations : N;
      buy_market_order_cancellations : N;
      sell_limit_order_cancellations : N;
      sell_market_order_cancellations : N;
      bid_ask_spread : N;
      vwap_buy : N;
      vwap_sell : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (start_time record < 256 ^ N.of_nat 8)%N /\
      (end_time record < 256 ^ N.of_nat 8)%N /\
      (buy_order_count record < 256 ^ N.of_nat 4)%N /\
      (sell_order_count record < 256 ^ N.of_nat 4)%N /\
      (buy_order_size record < 256 ^ N.of_nat 8)%N /\
      (sell_order_size record < 256 ^ N.of_nat 8)%N /\
      (buy_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (sell_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (buy_limit_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (buy_market_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (sell_limit_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (sell_market_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (bid_ask_spread record < 256 ^ N.of_nat 8)%N /\
      (vwap_buy record < 256 ^ N.of_nat 8)%N /\
      (vwap_sell record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (start_time record) ++
      encode_uint 8 (end_time record) ++
      encode_uint 4 (buy_order_count record) ++
      encode_uint 4 (sell_order_count record) ++
      encode_uint 8 (buy_order_size record) ++
      encode_uint 8 (sell_order_size record) ++
      encode_uint 4 (buy_order_cancellations record) ++
      encode_uint 4 (sell_order_cancellations record) ++
      encode_uint 4 (buy_limit_order_cancellations record) ++
      encode_uint 4 (buy_market_order_cancellations record) ++
      encode_uint 4 (sell_limit_order_cancellations record) ++
      encode_uint 4 (sell_market_order_cancellations record) ++
      encode_uint 8 (bid_ask_spread record) ++
      encode_uint 8 (vwap_buy record) ++
      encode_uint 8 (vwap_sell record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (start_time_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (end_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (buy_order_count_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (sell_order_count_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (buy_order_size_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (sell_order_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (buy_order_cancellations_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (sell_order_cancellations_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (buy_limit_order_cancellations_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (buy_market_order_cancellations_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (sell_limit_order_cancellations_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (sell_market_order_cancellations_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (bid_ask_spread_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (vwap_buy_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (vwap_sell_value, bytes) =>
                                                                              Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; start_time := start_time_value; end_time := end_time_value; buy_order_count := buy_order_count_value; sell_order_count := sell_order_count_value; buy_order_size := buy_order_size_value; sell_order_size := sell_order_size_value; buy_order_cancellations := buy_order_cancellations_value; sell_order_cancellations := sell_order_cancellations_value; buy_limit_order_cancellations := buy_limit_order_cancellations_value; buy_market_order_cancellations := buy_market_order_cancellations_value; sell_limit_order_cancellations := sell_limit_order_cancellations_value; sell_market_order_cancellations := sell_market_order_cancellations_value; bid_ask_spread := bid_ask_spread_value; vwap_buy := vwap_buy_value; vwap_sell := vwap_sell_value |}, bytes)
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
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 106.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AnalyticsMessage.

End TurquoiseReplayV244.
