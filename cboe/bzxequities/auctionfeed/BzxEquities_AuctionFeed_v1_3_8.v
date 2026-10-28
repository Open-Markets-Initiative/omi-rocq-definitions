From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Auction Feed

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
      - the dispatch that chooses a message by its type
      - a length prefix framing what follows
  *)

Module BzxEquitiesAuctionFeedV138.

  Module DebugPacket.

    (** Debug packets are intended to provide human readable text that may aid in debugging problems. *)
    Record t := {
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (text record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (text_value, bytes) =>
          Some ({| text := text_value |}, bytes)
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

  End DebugPacket.

  Module LoginAcceptedPacket.

    (** The Soup 2.0 server sends a Login Accepted Packet in response to receiving a valid Login Request  from the client. *)
    Record t := {
      session : list byte;
      sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      Datatypes.length (sequence_number record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_bytes 10 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              Some ({| session := session_value; sequence_number := sequence_number_value |}, bytes)
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

    (** The Soup 2.0 server sends this packet in response to an invalid Login Request Packet from the client. *)
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

    (** Sequenced Message Header *)
    Record t := {
      timestamp : list byte;
      sequenced_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (sequenced_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (timestamp record) ++
      encode_bytes 1 (sequenced_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sequenced_message_type_value, bytes) =>
              Some ({| timestamp := timestamp_value; sequenced_message_type := sequenced_message_type_value |}, bytes)
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

  Module AuctionUpdateMessage.

    (** Auction Update messages disseminate Cboe price and size information during auctions for Cboe listed securities and for CMC. *)
    Record t := {
      stock_symbol : list byte;
      auction_type : list byte;
      reference_price_short : list byte;
      buy_shares : list byte;
      sell_shares : list byte;
      indicative_price_short : list byte;
      auction_only_price_short : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (reference_price_short record) = 10 /\
      Datatypes.length (buy_shares record) = 10 /\
      Datatypes.length (sell_shares record) = 10 /\
      Datatypes.length (indicative_price_short record) = 10 /\
      Datatypes.length (auction_only_price_short record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 10 (reference_price_short record) ++
      encode_bytes 10 (buy_shares record) ++
      encode_bytes 10 (sell_shares record) ++
      encode_bytes 10 (indicative_price_short record) ++
      encode_bytes 10 (auction_only_price_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (reference_price_short_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (buy_shares_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (sell_shares_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (indicative_price_short_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (auction_only_price_short_value, bytes) =>
                                  Some ({| stock_symbol := stock_symbol_value; auction_type := auction_type_value; reference_price_short := reference_price_short_value; buy_shares := buy_shares_value; sell_shares := sell_shares_value; indicative_price_short := indicative_price_short_value; auction_only_price_short := auction_only_price_short_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
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

  End AuctionUpdateMessage.

  Module ExtendedAuctionUpdateMessage.

    (** The extended version of the Auction Update message accommodates larger prices. *)
    Record t := {
      stock_symbol : list byte;
      auction_type : list byte;
      reference_price_long : list byte;
      buy_shares : list byte;
      sell_shares : list byte;
      indicative_price_long : list byte;
      auction_only_price_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (reference_price_long record) = 14 /\
      Datatypes.length (buy_shares record) = 10 /\
      Datatypes.length (sell_shares record) = 10 /\
      Datatypes.length (indicative_price_long record) = 14 /\
      Datatypes.length (auction_only_price_long record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 14 (reference_price_long record) ++
      encode_bytes 10 (buy_shares record) ++
      encode_bytes 10 (sell_shares record) ++
      encode_bytes 14 (indicative_price_long record) ++
      encode_bytes 14 (auction_only_price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (reference_price_long_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (buy_shares_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (sell_shares_value, bytes) =>
                          match decode_bytes 14 bytes with
                          | None => None
                          | Some (indicative_price_long_value, bytes) =>
                              match decode_bytes 14 bytes with
                              | None => None
                              | Some (auction_only_price_long_value, bytes) =>
                                  Some ({| stock_symbol := stock_symbol_value; auction_type := auction_type_value; reference_price_long := reference_price_long_value; buy_shares := buy_shares_value; sell_shares := sell_shares_value; indicative_price_long := indicative_price_long_value; auction_only_price_long := auction_only_price_long_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End ExtendedAuctionUpdateMessage.

  Module AuctionSummaryMessage.

    (** Auction Summary messages disseminate the results of a Cboe listed security auction and for Cboe Market Close. *)
    Record t := {
      stock_symbol : list byte;
      auction_type : list byte;
      price_short : list byte;
      shares : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (shares record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 10 (shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (price_short_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (shares_value, bytes) =>
                      Some ({| stock_symbol := stock_symbol_value; auction_type := auction_type_value; price_short := price_short_value; shares := shares_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End AuctionSummaryMessage.

  Module ExtendedAuctionSummaryMessage.

    (** The extended version of the Auction Summary message accommodates larger prices. *)
    Record t := {
      stock_symbol : list byte;
      auction_type : list byte;
      price_long : list byte;
      shares : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (price_long record) = 14 /\
      Datatypes.length (shares record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 14 (price_long record) ++
      encode_bytes 10 (shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (shares_value, bytes) =>
                      Some ({| stock_symbol := stock_symbol_value; auction_type := auction_type_value; price_long := price_long_value; shares := shares_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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

  End ExtendedAuctionSummaryMessage.

  Module LoginRequestPacket.

    (** The Soup 2.0 client must send a Login Request Packet immediately upon establishing a new TCP/IP socket connection to the server. *)
    Record t := {
      username : list byte;
      password : list byte;
      requested_session : list byte;
      requested_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 10 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (requested_session_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End LoginRequestPacket.

End BzxEquitiesAuctionFeedV138.
