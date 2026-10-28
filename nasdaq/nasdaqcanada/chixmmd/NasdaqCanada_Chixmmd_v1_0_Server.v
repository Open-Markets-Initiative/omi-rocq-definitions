From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) CHIXMMD Multicast Market Data

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
      - the dispatch that chooses a message by its type
  *)

Module NasdaqCanadaChixmmdV10Server.

  Module ServerPacketHeader.

    (** SoupTcp Packet Header sent by the server *)
    Record t := {
      server_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (server_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (server_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (server_packet_type_value, bytes) =>
          Some ({| server_packet_type := server_packet_type_value |}, bytes)
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

  End ServerPacketHeader.

  Module LoginAcceptedPacket.

    (** The SoupTcp server sends a Login Accepted Packet in response to receiving a valid Login Request  from the client. *)
    Record t := {
      accepted_session : list byte;
      accepted_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (accepted_session record) = 10 /\
      Datatypes.length (accepted_sequence_number record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (accepted_session record) ++
      encode_bytes 10 (accepted_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (accepted_session_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (accepted_sequence_number_value, bytes) =>
              Some ({| accepted_session := accepted_session_value; accepted_sequence_number := accepted_sequence_number_value |}, bytes)
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

    (** The SoupTcp server sends this packet in response to an invalid Login Request Packet from the client. *)
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

  Module SequencedMessageHeader.

    (** Time and type carried ahead of every sequenced Itch message *)
    Record t := {
      timestamp : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (timestamp record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| timestamp := timestamp_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SequencedMessageHeader.

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (event_code_value, bytes) =>
          Some ({| event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module StockStatusMessage.

    (** At the start of each Canada GLIMPSE transmission, Nasdaq will disseminate stock status messages for all symbols in Nasdaq execution system for the current trading day. The Symbol Status spin may include halted issues. *)
    Record t := {
      stock : list byte;
      trading_state : list byte;
      reserved_1 : list byte;
      listing_market : list byte;
      board_lot_size : list byte;
      currency : list byte;
      gef_eligible : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (listing_market record) = 1 /\
      Datatypes.length (board_lot_size record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (gef_eligible record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (stock record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (listing_market record) ++
      encode_bytes 4 (board_lot_size record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (gef_eligible record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_state_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (listing_market_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (board_lot_size_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (currency_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (gef_eligible_value, bytes) =>
                                  Some ({| stock := stock_value; trading_state := trading_state_value; reserved_1 := reserved_1_value; listing_market := listing_market_value; board_lot_size := board_lot_size_value; currency := currency_value; gef_eligible := gef_eligible_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
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

  End StockStatusMessage.

  Module AddOrderMessage.

    (** An Add Order Message indicates that CXC or CX2 has accepted a visible order into the book. It includes a day-unique Order Reference key assigned to the order. The issuing of an Add Order Message is not necessarily always for a new order (see Modification of Existing Orders). Not applicable to CXD. *)
    Record t := {
      order_reference : list byte;
      buy_sell_indicator : list byte;
      shares : list byte;
      stock : list byte;
      price : list byte;
      broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (shares record) = 6 /\
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (price record) = 10 /\
      Datatypes.length (broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 6 (shares record) ++
      encode_bytes 10 (stock record) ++
      encode_bytes 10 (price record) ++
      encode_bytes 3 (broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (buy_sell_indicator_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (broker_value, bytes) =>
                              Some ({| order_reference := order_reference_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; broker := broker_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module LongFormAddOrderMessage.

    (** An Add Order Message indicates that CXC or CX2 has accepted a visible order into the book. It includes a day-unique Order Reference key assigned to the order. The issuing of an Add Order Message is not necessarily always for a new order (see Modification of Existing Orders). Not applicable to CXD. Long form messages are used when either the price or size is larger than the standard messages can permit. *)
    Record t := {
      order_reference : list byte;
      buy_sell_indicator : list byte;
      long_shares : list byte;
      stock : list byte;
      long_price : list byte;
      broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_reference record) = 9 /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      Datatypes.length (long_shares record) = 10 /\
      Datatypes.length (stock record) = 10 /\
      Datatypes.length (long_price record) = 19 /\
      Datatypes.length (broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (order_reference record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_bytes 10 (long_shares record) ++
      encode_bytes 10 (stock record) ++
      encode_bytes 19 (long_price record) ++
      encode_bytes 3 (broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (order_reference_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (buy_sell_indicator_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (long_shares_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_bytes 19 bytes with
                      | None => None
                      | Some (long_price_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (broker_value, bytes) =>
                              Some ({| order_reference := order_reference_value; buy_sell_indicator := buy_sell_indicator_value; long_shares := long_shares_value; stock := stock_value; long_price := long_price_value; broker := broker_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongFormAddOrderMessage.

End NasdaqCanadaChixmmdV10Server.
