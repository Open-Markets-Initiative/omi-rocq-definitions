From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Equity TotalView

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
      - a field read in bits
  *)

Module NordicEquitiesTotalViewV3001Server.

  Module ServerPacketHeader.

    (** Packet header of a packet sent by the server *)
    Record t := {
      packet_length : N;
      server_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (server_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (server_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (server_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; server_packet_type := server_packet_type_value |}, bytes)
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

  End ServerPacketHeader.

  Module LoginAcceptedPacket.

    (** The SoupBinTCP server sends a Login Accepted Packet in response to receiving a valid Login Request from the client *)
    Record t := {
      accepted_session : list byte;
      accepted_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (accepted_session record) = 10 /\
      Datatypes.length (accepted_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (accepted_session record) ++
      encode_bytes 20 (accepted_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (accepted_session_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (accepted_sequence_number_value, bytes) =>
              Some ({| accepted_session := accepted_session_value; accepted_sequence_number := accepted_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End LoginAcceptedPacket.

  Module LoginRejectedPacket.

    (** The SoupBinTCP server sends this packet in response to an invalid Login Request Packet from the client *)
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

  End LoginRejectedPacket.

  Module SystemEventMessage.

    (** Signals a market or data feed handler event *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; event_code := event_code_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module OrderBookTradingActionMessage.

    (** Indicates the current trading status of a security *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_book : N;
      symbol_state : list byte;
      extension : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_state record) = 1 /\
      Datatypes.length (extension record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (order_book record) ++
      encode_bytes 1 (symbol_state record) ++
      encode_bytes 1 (extension record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (symbol_state_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (extension_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (reason_value, bytes) =>
                              Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_book := order_book_value; symbol_state := symbol_state_value; extension := extension_value; reason := reason_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookTradingActionMessage.

  Module AddOrderMessage.

    (** An order added to the book without Mpid attribution *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      quantity : N;
      order_book : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (buy_sell_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; quantity := quantity_value; order_book := order_book_value; price := price_value |}, bytes)
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module AddOrderMpidAttributionMessage.

    (** An order added to the book with Mpid attribution *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      quantity : N;
      order_book : N;
      price : N;
      attribution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (attribution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (price record) ++
      encode_bytes 4 (attribution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_reference_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (buy_sell_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (attribution_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; quantity := quantity_value; order_book := order_book_value; price := price_value; attribution := attribution_value |}, bytes)
                                  end
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMpidAttributionMessage.

  Module EndOfSnapshotMessage.

    (** Denotes the TotalView Itch sequence number to begin real time processing from *)
    Record t := {
      sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          Some ({| sequence_number := sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End EndOfSnapshotMessage.

End NordicEquitiesTotalViewV3001Server.
