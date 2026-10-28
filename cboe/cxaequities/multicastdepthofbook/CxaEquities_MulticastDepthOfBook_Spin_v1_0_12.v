From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Multicast Depth Of Book

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
      - a Reassemble rule
      - a run filling what frames it
  *)

Module CxaEquitiesMulticastDepthOfBookV1012.

  Module PacketHeader.

    Record t := {
      length_ : N;
      message_count : N;
      unit_ : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (unit_ record < 256 ^ N.of_nat 1)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (unit_ record) ++
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (unit__value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; unit_ := unit__value; sequence := sequence_value |}, bytes)
                  end
              end
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 1)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module LoginMessage.

    (** First message sent to the Spin Server by the client process after the connection to the Spin Server is established. Failure to login before sending any other message type will result in the connection being dropped by the Spin Server. Identical format to the GRP Login message. *)
    Record t := {
      session_sub_id : list byte;
      username : list byte;
      filler : list byte;
      password : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_sub_id record) = 4 /\
      Datatypes.length (username record) = 4 /\
      Datatypes.length (filler record) = 2 /\
      Datatypes.length (password record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (session_sub_id record) ++
      encode_bytes 4 (username record) ++
      encode_bytes 2 (filler record) ++
      encode_bytes 10 (password record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (session_sub_id_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (username_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (password_value, bytes) =>
                      Some ({| session_sub_id := session_sub_id_value; username := username_value; filler := filler_value; password := password_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginMessage.

  Module LoginResponseMessage.

    (** Sent by the Spin Server to the client process in response to a Login message. The Status field reflects an accepted login or the reason the session was not accepted. If login fails, the connection will be dropped after the Login Response message is sent. *)
    Record t := {
      login_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_response_status_value, bytes) =>
          Some ({| login_response_status := login_response_status_value |}, bytes)
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

  Module SpinImageAvailableMessage.

    (** Sent once per second by the Spin Server, indicating through what sequence number a spin is available. *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End SpinImageAvailableMessage.

  Module SpinRequestMessage.

    (** Used by a client's process to request transmission of a spin of the unit's order book. *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End SpinRequestMessage.

  Module SpinResponseMessage.

    (** Sent by the Spin Server in response to a client's Spin Request message indicating whether a spin will be sent. *)
    Record t := {
      sequence : N;
      order_count : N;
      spin_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (spin_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record) ++
      encode_uint 4 (order_count record) ++
      encode_bytes 1 (spin_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (spin_response_status_value, bytes) =>
                  Some ({| sequence := sequence_value; order_count := order_count_value; spin_response_status := spin_response_status_value |}, bytes)
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

  End SpinResponseMessage.

  Module SpinFinishedMessage.

    (** Sent to indicate that all messages for the spin requested have been sent. A Spin Finished message is only sent if a Spin Request was not rejected. Upon receipt, any buffered multicast messages should be applied to the client's copy of the book to make it current. *)
    Record t := {
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_value, bytes) =>
          Some ({| sequence := sequence_value |}, bytes)
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

  End SpinFinishedMessage.

  Module TradingStatusMessage.

    (** Indicates the current trading status of a security. Included in a spin response so the client can populate trading state for each symbol. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      trading_status : list byte;
      market_id_code : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (market_id_code record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 4 (market_id_code record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_id_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol := symbol_value; trading_status := trading_status_value; market_id_code := market_id_code_value; reserved_1 := reserved_1_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module AddOrderMessage.

    (** Represents an open order on the CXA book. Included in a spin response to reconstruct the open order book at the spin sequence number. *)
    Record t := {
      timestamp : N;
      order_id : N;
      side_indicator : list byte;
      quantity : N;
      symbol : list byte;
      price : N;
      pid : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (pid record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (price record) ++
      encode_bytes 4 (pid record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (pid_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (reserved_1_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity := quantity_value; symbol := symbol_value; price := price_value; pid := pid_value; reserved_1 := reserved_1_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module CalculatedValueMessage.

    (** Carries the latest calculated market value for a specified symbol. Included in a spin response so the client can populate the latest index, iNAV, or closing price value. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      value_category : list byte;
      value : N;
      value_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (value_category record) = 1 /\
      (value record < 256 ^ N.of_nat 8)%N /\
      (value_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (value_category record) ++
      encode_uint 8 (value record) ++
      encode_uint 8 (value_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (value_category_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (value_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (value_timestamp_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol := symbol_value; value_category := value_category_value; value := value_value; value_timestamp := value_timestamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CalculatedValueMessage.

  Module AuctionUpdateMessage.

    (** Provides the latest indicative auction price and eligible shares for a symbol in an overlapping order book state. Included in a spin response so the client can populate the current auction state. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      auction_type : list byte;
      buy_shares : N;
      sell_shares : N;
      indicative_price : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (auction_type record) = 1 /\
      (buy_shares record < 256 ^ N.of_nat 4)%N /\
      (sell_shares record < 256 ^ N.of_nat 4)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (buy_shares record) ++
      encode_uint 4 (sell_shares record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (buy_shares_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sell_shares_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (indicative_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserved_1_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; symbol := symbol_value; auction_type := auction_type_value; buy_shares := buy_shares_value; sell_shares := sell_shares_value; indicative_price := indicative_price_value; reserved_1 := reserved_1_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionUpdateMessage.

End CxaEquitiesMulticastDepthOfBookV1012.
