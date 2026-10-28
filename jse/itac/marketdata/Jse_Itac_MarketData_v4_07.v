From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * JSE Limited Market Data

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
      - a run counted by a field
      - a field read in bits
  *)

Module JseItacMarketDataV407.

  Module UnitHeader.

    (** Jse Mitch Udp Unit Header *)
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

    (** Jse Mitch Udp Message Header *)
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

    (** Sent by the client to log in to the market data gateway. *)
    Record t := {
      username : list byte;
      password : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              Some ({| username := username_value; password := password_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End LoginRequestMessage.

  Module ReplayRequestMessage.

    (** Sent by the client on the replay channel to request retransmission of a range of messages. *)
    Record t := {
      market_data_group : list byte;
      first_message : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_data_group record) = 1 /\
      (first_message record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_data_group record) ++
      encode_uint 4 (first_message record) ++
      encode_uint 2 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (first_message_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (count_value, bytes) =>
                  Some ({| market_data_group := market_data_group_value; first_message := first_message_value; count := count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplayRequestMessage.

  Module LoginResponseMessage.

    (** Sent by the server in response to a Login Request. *)
    Record t := {
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (status_value, bytes) =>
          Some ({| status := status_value |}, bytes)
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

    (** Sent by the server in response to a Replay Request. *)
    Record t := {
      market_data_group : list byte;
      first_message : N;
      count : N;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_data_group record) = 1 /\
      (first_message record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_data_group record) ++
      encode_uint 4 (first_message record) ++
      encode_uint 2 (count record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (first_message_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (count_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (status_value, bytes) =>
                      Some ({| market_data_group := market_data_group_value; first_message := first_message_value; count := count_value; status := status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReplayResponseMessage.

  Module SnapshotResponseMessage.

    (** Sent by the server in response to a Snapshot Request. *)
    Record t := {
      sequence_number : N;
      order_count : N;
      status : list byte;
      snapshot_type : N;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (status record) = 1 /\
      (snapshot_type record < 256 ^ N.of_nat 1)%N /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (order_count record) ++
      encode_bytes 1 (status record) ++
      encode_uint 1 (snapshot_type record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (snapshot_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (request_id_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; order_count := order_count_value; status := status_value; snapshot_type := snapshot_type_value; request_id := request_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End SnapshotResponseMessage.

  Module TimeMessage.

    (** Sent for every second in which at least one application message is generated. All subsequent messages carry a nanosecond offset from this time. *)
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

  End TimeMessage.

  Module SystemEventMessage.

    (** Sent to signal the start and end of the trading day. *)
    Record t := {
      nanosecond : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| nanosecond := nanosecond_value; event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module OrderDeletedMessage.

    (** Sent when an order is removed from the order book. *)
    Record t := {
      nanosecond : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              Some ({| nanosecond := nanosecond_value; order_id := order_id_value |}, bytes)
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

  End OrderDeletedMessage.

  Module OrderBookClearMessage.

    (** Sent to instruct the recipient to discard every order held for an instrument on the named book. *)
    Record t := {
      nanosecond : N;
      instrument_id : N;
      sub_book : N;
      book_level : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (sub_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (book_level record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (sub_book record) ++
      encode_bytes 1 (book_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (sub_book_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (book_level_value, bytes) =>
                      Some ({| nanosecond := nanosecond_value; instrument_id := instrument_id_value; sub_book := sub_book_value; book_level := book_level_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End OrderBookClearMessage.

  Module OrderExecutedMessage.

    (** Sent when an order on the book executes in full or in part at its display price. *)
    Record t := {
      nanosecond : N;
      order_id : N;
      executed_quantity : N;
      trade_id : N;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
      venue_of_execution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (venue_of_execution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record) ++
      encode_bytes 4 (venue_of_execution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_opt_px_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (volatility_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (underlying_reference_price_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (venue_of_execution_value, bytes) =>
                                      Some ({| nanosecond := nanosecond_value; order_id := order_id_value; executed_quantity := executed_quantity_value; trade_id := trade_id_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value; venue_of_execution := venue_of_execution_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceSizeMessage.

    (** Sent when an order on the book executes at a price other than its display price, or when the execution is not printable. *)
    Record t := {
      nanosecond : N;
      order_id : N;
      executed_quantity : N;
      display_quantity : N;
      trade_id : N;
      printable : list byte;
      price : N;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
      venue_of_execution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (display_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (venue_of_execution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (display_quantity record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record) ++
      encode_bytes 4 (venue_of_execution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (display_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (printable_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_opt_px_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (volatility_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (underlying_reference_price_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (venue_of_execution_value, bytes) =>
                                                  Some ({| nanosecond := nanosecond_value; order_id := order_id_value; executed_quantity := executed_quantity_value; display_quantity := display_quantity_value; trade_id := trade_id_value; printable := printable_value; price := price_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value; venue_of_execution := venue_of_execution_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceSizeMessage.

  Module AuctionTradeMessage.

    (** Sent for a trade that results from an auction uncrossing. *)
    Record t := {
      nanosecond : N;
      quantity : N;
      instrument_id : N;
      reserved_a : N;
      reserved_b : N;
      price : N;
      trade_id : N;
      auction_type : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
      pt_cancellation_flag : list byte;
      pt_amendment_flag : list byte;
      venue_of_execution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_a record < 256 ^ N.of_nat 1)%N /\
      (reserved_b record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (pt_cancellation_flag record) = 4 /\
      Datatypes.length (pt_amendment_flag record) = 4 /\
      Datatypes.length (venue_of_execution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (reserved_a record) ++
      encode_uint 1 (reserved_b record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record) ++
      encode_bytes 4 (pt_cancellation_flag record) ++
      encode_bytes 4 (pt_amendment_flag record) ++
      encode_bytes 4 (venue_of_execution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_a_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_b_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (auction_type_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_opt_px_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (volatility_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (underlying_reference_price_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (pt_cancellation_flag_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (pt_amendment_flag_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (venue_of_execution_value, bytes) =>
                                                              Some ({| nanosecond := nanosecond_value; quantity := quantity_value; instrument_id := instrument_id_value; reserved_a := reserved_a_value; reserved_b := reserved_b_value; price := price_value; trade_id := trade_id_value; auction_type := auction_type_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value; pt_cancellation_flag := pt_cancellation_flag_value; pt_amendment_flag := pt_amendment_flag_value; venue_of_execution := venue_of_execution_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionTradeMessage.

  Module OffBookTradeMessage.

    (** Sent for a trade agreed away from the order book and reported to the exchange. *)
    Record t := {
      nanosecond : N;
      executed_quantity : N;
      instrument_id : N;
      reserved_a : N;
      reserved_b : N;
      price : N;
      trade_id : N;
      off_book_trade_type : list byte;
      trade_time : list byte;
      trade_date : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
      pt_cancellation_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_a record < 256 ^ N.of_nat 1)%N /\
      (reserved_b record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (off_book_trade_type record) = 4 /\
      Datatypes.length (trade_time record) = 8 /\
      Datatypes.length (trade_date record) = 8 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (pt_cancellation_flag record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (reserved_a record) ++
      encode_uint 1 (reserved_b record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 4 (off_book_trade_type record) ++
      encode_bytes 8 (trade_time record) ++
      encode_bytes 8 (trade_date record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record) ++
      encode_bytes 4 (pt_cancellation_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_a_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_b_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (off_book_trade_type_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (trade_time_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (trade_date_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (last_opt_px_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (volatility_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (underlying_reference_price_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (pt_cancellation_flag_value, bytes) =>
                                                              Some ({| nanosecond := nanosecond_value; executed_quantity := executed_quantity_value; instrument_id := instrument_id_value; reserved_a := reserved_a_value; reserved_b := reserved_b_value; price := price_value; trade_id := trade_id_value; off_book_trade_type := off_book_trade_type_value; trade_time := trade_time_value; trade_date := trade_date_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value; pt_cancellation_flag := pt_cancellation_flag_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OffBookTradeMessage.

  Module AuctionInfoMessage.

    (** Disseminates the indicative price and paired quantity of an instrument in an auction call. *)
    Record t := {
      nanosecond : N;
      paired_quantity : N;
      reserved_4 : N;
      imbalance_direction : list byte;
      instrument_id : N;
      reserved_a : N;
      reserved_b : N;
      price : N;
      auction_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (paired_quantity record < 256 ^ N.of_nat 4)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (imbalance_direction record) = 1 /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_a record < 256 ^ N.of_nat 1)%N /\
      (reserved_b record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (paired_quantity record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (reserved_a record) ++
      encode_uint 1 (reserved_b record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (auction_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (paired_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (reserved_4_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (imbalance_direction_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_a_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserved_b_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (auction_type_value, bytes) =>
                                          Some ({| nanosecond := nanosecond_value; paired_quantity := paired_quantity_value; reserved_4 := reserved_4_value; imbalance_direction := imbalance_direction_value; instrument_id := instrument_id_value; reserved_a := reserved_a_value; reserved_b := reserved_b_value; price := price_value; auction_type := auction_type_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionInfoMessage.

  Module StatisticsMessage.

    (** Disseminates the opening or closing price of an instrument. *)
    Record t := {
      nanosecond : N;
      instrument_id : N;
      reserved_a : N;
      reserved_b : N;
      statistic_type : list byte;
      price : N;
      open_close_indicator : list byte;
      sub_book : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_a record < 256 ^ N.of_nat 1)%N /\
      (reserved_b record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (statistic_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (open_close_indicator record) = 1 /\
      (sub_book record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (reserved_a record) ++
      encode_uint 1 (reserved_b record) ++
      encode_bytes 1 (statistic_type record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (open_close_indicator record) ++
      encode_uint 1 (sub_book record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reserved_a_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_b_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (statistic_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (open_close_indicator_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (sub_book_value, bytes) =>
                                      Some ({| nanosecond := nanosecond_value; instrument_id := instrument_id_value; reserved_a := reserved_a_value; reserved_b := reserved_b_value; statistic_type := statistic_type_value; price := price_value; open_close_indicator := open_close_indicator_value; sub_book := sub_book_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticsMessage.

  Module ExtendedStatisticsMessage.

    (** Disseminates the intraday statistics of an instrument. Values that are not set or have been withdrawn are negative, except Volume and Number of Trades which are zero. *)
    Record t := {
      nanosecond : N;
      instrument_id : N;
      high_price : N;
      low_price : N;
      vwap : N;
      volume : N;
      turnover : N;
      number_of_trades : N;
      reserved_8 : N;
      sub_book : N;
      notional_exposure : N;
      notional_delta_exposure : N;
      open_interest : N;
      theoretical_price : N;
      delta : N;
      gamma : N;
      vega : N;
      theta : N;
      rho : N;
      volatility : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (number_of_trades record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      (sub_book record < 256 ^ N.of_nat 1)%N /\
      (notional_exposure record < 256 ^ N.of_nat 8)%N /\
      (notional_delta_exposure record < 256 ^ N.of_nat 8)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N /\
      (theoretical_price record < 256 ^ N.of_nat 8)%N /\
      (delta record < 256 ^ N.of_nat 8)%N /\
      (gamma record < 256 ^ N.of_nat 8)%N /\
      (vega record < 256 ^ N.of_nat 8)%N /\
      (theta record < 256 ^ N.of_nat 8)%N /\
      (rho record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 4 (number_of_trades record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_uint 1 (sub_book record) ++
      encode_uint 8 (notional_exposure record) ++
      encode_uint 8 (notional_delta_exposure record) ++
      encode_uint 8 (open_interest record) ++
      encode_uint 8 (theoretical_price record) ++
      encode_uint 8 (delta record) ++
      encode_uint 8 (gamma record) ++
      encode_uint 8 (vega record) ++
      encode_uint 8 (theta record) ++
      encode_uint 8 (rho record) ++
      encode_uint 8 (volatility record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (high_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (vwap_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (turnover_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (number_of_trades_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (reserved_8_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (sub_book_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (notional_exposure_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (notional_delta_exposure_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (open_interest_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (theoretical_price_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (delta_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (gamma_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (vega_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (theta_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (rho_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (volatility_value, bytes) =>
                                                                                      Some ({| nanosecond := nanosecond_value; instrument_id := instrument_id_value; high_price := high_price_value; low_price := low_price_value; vwap := vwap_value; volume := volume_value; turnover := turnover_value; number_of_trades := number_of_trades_value; reserved_8 := reserved_8_value; sub_book := sub_book_value; notional_exposure := notional_exposure_value; notional_delta_exposure := notional_delta_exposure_value; open_interest := open_interest_value; theoretical_price := theoretical_price_value; delta := delta_value; gamma := gamma_value; vega := vega_value; theta := theta_value; rho := rho_value; volatility := volatility_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 137.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ExtendedStatisticsMessage.

  Module NewsMessage.

    (** Carries an exchange announcement and the instruments it relates to. *)
    Record t := {
      nanosecond : N;
      time : list byte;
      urgency : list byte;
      headline : list byte;
      text : list byte;
      instruments : list byte;
      underlyings : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time record) = 8 /\
      Datatypes.length (urgency record) = 1 /\
      Datatypes.length (headline record) = 100 /\
      Datatypes.length (text record) = 750 /\
      Datatypes.length (instruments record) = 100 /\
      Datatypes.length (underlyings record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 8 (time record) ++
      encode_bytes 1 (urgency record) ++
      encode_bytes 100 (headline record) ++
      encode_bytes 750 (text record) ++
      encode_bytes 100 (instruments record) ++
      encode_bytes 100 (underlyings record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (urgency_value, bytes) =>
                  match decode_bytes 100 bytes with
                  | None => None
                  | Some (headline_value, bytes) =>
                      match decode_bytes 750 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          match decode_bytes 100 bytes with
                          | None => None
                          | Some (instruments_value, bytes) =>
                              match decode_bytes 100 bytes with
                              | None => None
                              | Some (underlyings_value, bytes) =>
                                  Some ({| nanosecond := nanosecond_value; time := time_value; urgency := urgency_value; headline := headline_value; text := text_value; instruments := instruments_value; underlyings := underlyings_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1063.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewsMessage.

  Module IndicativeQuoteInfoMessage.

    (** Disseminates the indicative bid and offer of a request for quote. *)
    Record t := {
      nanosecond : N;
      instrument_id : N;
      rfq_id : list byte;
      indicative_bid_price : N;
      indicative_offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (rfq_id record) = 10 /\
      (indicative_bid_price record < 256 ^ N.of_nat 8)%N /\
      (indicative_offer_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 10 (rfq_id record) ++
      encode_uint 8 (indicative_bid_price record) ++
      encode_uint 8 (indicative_offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (rfq_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (indicative_bid_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (indicative_offer_price_value, bytes) =>
                          Some ({| nanosecond := nanosecond_value; instrument_id := instrument_id_value; rfq_id := rfq_id_value; indicative_bid_price := indicative_bid_price_value; indicative_offer_price := indicative_offer_price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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

  End IndicativeQuoteInfoMessage.

End JseItacMarketDataV407.
