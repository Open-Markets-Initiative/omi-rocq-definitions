From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) 

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
      - a run counted by a field
      - a field of no fixed width
      - a length prefix framing what follows
  *)

Module NasdaqUtpInputV40Client.

  Module ClientTcpPacketHeader.

    (** Packet header of a packet sent by the client *)
    Record t := {
      packet_length : N;
      client_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (client_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (client_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (client_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; client_packet_type := client_packet_type_value |}, bytes)
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

  End ClientTcpPacketHeader.

  Module MessageHeader.

    (** UTP Participant Input message header — fixed Version + Message Category prefix common to inbound and return messages *)
    Record t := {
      version : N;
      message_category : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_category record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_bytes 1 (message_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_category_value, bytes) =>
              Some ({| version := version_value; message_category := message_category_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module ProtectedExchangeQuoteMessageShortFormMessage.

    (** Short-format Exchange Quotation Message (QQ). Transmits Bid and Ask price and size from an Exchange to the SIP. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_short : list byte;
      bid_short : N;
      bid_size_short : N;
      ask_short : N;
      ask_size_short : N;
      cond : list byte;
      rii : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 5 /\
      (bid_short record < 256 ^ N.of_nat 2)%N /\
      (bid_size_short record < 256 ^ N.of_nat 2)%N /\
      (ask_short record < 256 ^ N.of_nat 2)%N /\
      (ask_size_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (cond record) = 1 /\
      Datatypes.length (rii record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 5 (symbol_short record) ++
      encode_uint 2 (bid_short record) ++
      encode_uint 2 (bid_size_short record) ++
      encode_uint 2 (ask_short record) ++
      encode_uint 2 (ask_size_short record) ++
      encode_bytes 1 (cond record) ++
      encode_bytes 1 (rii record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (symbol_short_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (bid_short_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (bid_size_short_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ask_short_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_size_short_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cond_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (rii_value, bytes) =>
                                                  Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_short := symbol_short_value; bid_short := bid_short_value; bid_size_short := bid_size_short_value; ask_short := ask_short_value; ask_size_short := ask_size_short_value; cond := cond_value; rii := rii_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ProtectedExchangeQuoteMessageShortFormMessage.

  Module ProtectedExchangeQuoteMessageLongFormMessage.

    (** Long-format Exchange Quotation Message (QL). *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      bid_long : N;
      bid_size_long : N;
      ask_long : N;
      ask_size_long : N;
      cond : list byte;
      rii : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (bid_long record < 256 ^ N.of_nat 8)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask_long record < 256 ^ N.of_nat 8)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cond record) = 1 /\
      Datatypes.length (rii record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 8 (bid_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 8 (ask_long record) ++
      encode_uint 4 (ask_size_long record) ++
      encode_bytes 1 (cond record) ++
      encode_bytes 1 (rii record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bid_size_long_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (ask_long_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (ask_size_long_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cond_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (rii_value, bytes) =>
                                                  Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; bid_long := bid_long_value; bid_size_long := bid_size_long_value; ask_long := ask_long_value; ask_size_long := ask_size_long_value; cond := cond_value; rii := rii_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ProtectedExchangeQuoteMessageLongFormMessage.

  Module FinraProtectedQuoteMessageWithBboInfoMessage.

    (** FINRA BBO Quote Message w BBO Info (QG). *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      bid_long : N;
      bid_size_long : N;
      ask_long : N;
      ask_size_long : N;
      cond : list byte;
      mpid : list byte;
      bbo_bid : N;
      bbo_bid_size : N;
      bbo_bid_mpid : list byte;
      bbo_ask : N;
      bbo_ask_size : N;
      bbo_ask_mpid : list byte;
      bbo_cond : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (bid_long record < 256 ^ N.of_nat 8)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask_long record < 256 ^ N.of_nat 8)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cond record) = 1 /\
      Datatypes.length (mpid record) = 4 /\
      (bbo_bid record < 256 ^ N.of_nat 8)%N /\
      (bbo_bid_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bbo_bid_mpid record) = 4 /\
      (bbo_ask record < 256 ^ N.of_nat 8)%N /\
      (bbo_ask_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bbo_ask_mpid record) = 4 /\
      Datatypes.length (bbo_cond record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 8 (bid_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 8 (ask_long record) ++
      encode_uint 4 (ask_size_long record) ++
      encode_bytes 1 (cond record) ++
      encode_bytes 4 (mpid record) ++
      encode_uint 8 (bbo_bid record) ++
      encode_uint 4 (bbo_bid_size record) ++
      encode_bytes 4 (bbo_bid_mpid record) ++
      encode_uint 8 (bbo_ask record) ++
      encode_uint 4 (bbo_ask_size record) ++
      encode_bytes 4 (bbo_ask_mpid record) ++
      encode_bytes 1 (bbo_cond record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (bid_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (bid_size_long_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (ask_long_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (ask_size_long_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cond_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (mpid_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (bbo_bid_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (bbo_bid_size_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (bbo_bid_mpid_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (bbo_ask_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (bbo_ask_size_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (bbo_ask_mpid_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (bbo_cond_value, bytes) =>
                                                                                  Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; bid_long := bid_long_value; bid_size_long := bid_size_long_value; ask_long := ask_long_value; ask_size_long := ask_size_long_value; cond := cond_value; mpid := mpid_value; bbo_bid := bbo_bid_value; bbo_bid_size := bbo_bid_size_value; bbo_bid_mpid := bbo_bid_mpid_value; bbo_ask := bbo_ask_value; bbo_ask_size := bbo_ask_size_value; bbo_ask_mpid := bbo_ask_mpid_value; bbo_cond := bbo_cond_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 107.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
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
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FinraProtectedQuoteMessageWithBboInfoMessage.

  Module FinraProtectedQuoteMessageWithoutBboInfoMessage.

    (** FINRA BBO Quote Message without BBO Info (QF). *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      bid_long : N;
      bid_size_long : N;
      ask_long : N;
      ask_size_long : N;
      cond : list byte;
      mpid : list byte;
      bbo_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (bid_long record < 256 ^ N.of_nat 8)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask_long record < 256 ^ N.of_nat 8)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cond record) = 1 /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (bbo_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 8 (bid_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 8 (ask_long record) ++
      encode_uint 4 (ask_size_long record) ++
      encode_bytes 1 (cond record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 1 (bbo_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (bid_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (bid_size_long_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (ask_long_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (ask_size_long_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (cond_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (mpid_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (bbo_indicator_value, bytes) =>
                                                          Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; bid_long := bid_long_value; bid_size_long := bid_size_long_value; ask_long := ask_long_value; ask_size_long := ask_size_long_value; cond := cond_value; mpid := mpid_value; bbo_indicator := bbo_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 75.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
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
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FinraProtectedQuoteMessageWithoutBboInfoMessage.

  Module RegularTradeReportMessage.

    (** Regular Trade Report Message (TE). Carries whole-share last sale reports from an Exchange to the SIP. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      trade_id : N;
      tt_exempt : list byte;
      trcond : list byte;
      ssday : N;
      side : list byte;
      price : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tt_exempt record) = 1 /\
      Datatypes.length (trcond record) = 4 /\
      (ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trade_id record) ++
      encode_bytes 1 (tt_exempt record) ++
      encode_bytes 4 (trcond record) ++
      encode_uint 2 (ssday record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (tt_exempt_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (trcond_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (ssday_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (volume_value, bytes) =>
                                                          Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; trade_id := trade_id_value; tt_exempt := tt_exempt_value; trcond := trcond_value; ssday := ssday_value; side := side_value; price := price_value; volume := volume_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegularTradeReportMessage.

  Module TradeCancelErrorMessage.

    (** Trade Cancel/Error Message (TI). Cancels or errors a previously delivered trade. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      cancel_type : list byte;
      orig_trade_id : N;
      orig_tt_exempt : list byte;
      orig_trcond : list byte;
      orig_ssday : N;
      orig_side : list byte;
      orig_price : N;
      orig_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (cancel_type record) = 1 /\
      (orig_trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_tt_exempt record) = 1 /\
      Datatypes.length (orig_trcond record) = 4 /\
      (orig_ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (orig_side record) = 1 /\
      (orig_price record < 256 ^ N.of_nat 8)%N /\
      (orig_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (cancel_type record) ++
      encode_uint 4 (orig_trade_id record) ++
      encode_bytes 1 (orig_tt_exempt record) ++
      encode_bytes 4 (orig_trcond record) ++
      encode_uint 2 (orig_ssday record) ++
      encode_bytes 1 (orig_side record) ++
      encode_uint 8 (orig_price record) ++
      encode_uint 4 (orig_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cancel_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (orig_trade_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (orig_tt_exempt_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (orig_trcond_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (orig_ssday_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (orig_side_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (orig_price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (orig_volume_value, bytes) =>
                                                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; cancel_type := cancel_type_value; orig_trade_id := orig_trade_id_value; orig_tt_exempt := orig_tt_exempt_value; orig_trcond := orig_trcond_value; orig_ssday := orig_ssday_value; orig_side := orig_side_value; orig_price := orig_price_value; orig_volume := orig_volume_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelErrorMessage.

  Module TradeCorrectionMessage.

    (** Trade Correction Message (TJ). Corrects a previously delivered trade with new values. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      trade_id : N;
      orig_trade_id : N;
      orig_tt_exempt : list byte;
      orig_trcond : list byte;
      orig_ssday : N;
      side : list byte;
      orig_price : N;
      orig_volume : N;
      new_tt_exempt : list byte;
      new_trcond : list byte;
      new_ssday : N;
      new_price : N;
      new_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (orig_trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_tt_exempt record) = 1 /\
      Datatypes.length (orig_trcond record) = 4 /\
      (orig_ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (orig_price record < 256 ^ N.of_nat 8)%N /\
      (orig_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (new_tt_exempt record) = 1 /\
      Datatypes.length (new_trcond record) = 4 /\
      (new_ssday record < 256 ^ N.of_nat 2)%N /\
      (new_price record < 256 ^ N.of_nat 8)%N /\
      (new_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (orig_trade_id record) ++
      encode_bytes 1 (orig_tt_exempt record) ++
      encode_bytes 4 (orig_trcond record) ++
      encode_uint 2 (orig_ssday record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (orig_price record) ++
      encode_uint 4 (orig_volume record) ++
      encode_bytes 1 (new_tt_exempt record) ++
      encode_bytes 4 (new_trcond record) ++
      encode_uint 2 (new_ssday record) ++
      encode_uint 8 (new_price record) ++
      encode_uint 4 (new_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (orig_trade_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (orig_tt_exempt_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (orig_trcond_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (orig_ssday_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (side_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (orig_price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (orig_volume_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (new_tt_exempt_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (new_trcond_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (new_ssday_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (new_price_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (new_volume_value, bytes) =>
                                                                                  Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; trade_id := trade_id_value; orig_trade_id := orig_trade_id_value; orig_tt_exempt := orig_tt_exempt_value; orig_trcond := orig_trcond_value; orig_ssday := orig_ssday_value; side := side_value; orig_price := orig_price_value; orig_volume := orig_volume_value; new_tt_exempt := new_tt_exempt_value; new_trcond := new_trcond_value; new_ssday := new_ssday_value; new_price := new_price_value; new_volume := new_volume_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 92.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module AsOfTradeReportMessage.

    (** As/Of Trade Report Message (TH). Reports a trade from a prior session date. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      trade_id : N;
      tt_exempt : list byte;
      trcond : list byte;
      ssday : N;
      side : list byte;
      price : N;
      volume : N;
      trade_time : N;
      reversal : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tt_exempt record) = 1 /\
      Datatypes.length (trcond record) = 4 /\
      (ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reversal record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trade_id record) ++
      encode_bytes 1 (tt_exempt record) ++
      encode_bytes 4 (trcond record) ++
      encode_uint 2 (ssday record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (trade_time record) ++
      encode_bytes 1 (reversal record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tt_exempt_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (trcond_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ssday_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (side_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (volume_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (trade_time_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (reversal_value, bytes) =>
                                                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; trade_id := trade_id_value; tt_exempt := tt_exempt_value; trcond := trcond_value; ssday := ssday_value; side := side_value; price := price_value; volume := volume_value; trade_time := trade_time_value; reversal := reversal_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AsOfTradeReportMessage.

  Module FractionalRegularTradeReportMessage.

    (** Fractional Regular Trade Report Message (TK). Last sale report with implied 6-decimal fractional volume. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      trade_id : N;
      tt_exempt : list byte;
      trcond : list byte;
      ssday : N;
      side : list byte;
      price : N;
      volume_fractional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tt_exempt record) = 1 /\
      Datatypes.length (trcond record) = 4 /\
      (ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume_fractional record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trade_id record) ++
      encode_bytes 1 (tt_exempt record) ++
      encode_bytes 4 (trcond record) ++
      encode_uint 2 (ssday record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (volume_fractional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (tt_exempt_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (trcond_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (ssday_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (side_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (volume_fractional_value, bytes) =>
                                                          Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; trade_id := trade_id_value; tt_exempt := tt_exempt_value; trcond := trcond_value; ssday := ssday_value; side := side_value; price := price_value; volume_fractional := volume_fractional_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalRegularTradeReportMessage.

  Module FractionalTradeCancelErrorMessage.

    (** Fractional Trade Cancel/Error Message (TO). *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      cancel_type : list byte;
      orig_trade_id : N;
      orig_tt_exempt : list byte;
      orig_trcond : list byte;
      orig_ssday : N;
      orig_side : list byte;
      orig_price : N;
      orig_volume_fractional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (cancel_type record) = 1 /\
      (orig_trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_tt_exempt record) = 1 /\
      Datatypes.length (orig_trcond record) = 4 /\
      (orig_ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (orig_side record) = 1 /\
      (orig_price record < 256 ^ N.of_nat 8)%N /\
      (orig_volume_fractional record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (cancel_type record) ++
      encode_uint 4 (orig_trade_id record) ++
      encode_bytes 1 (orig_tt_exempt record) ++
      encode_bytes 4 (orig_trcond record) ++
      encode_uint 2 (orig_ssday record) ++
      encode_bytes 1 (orig_side record) ++
      encode_uint 8 (orig_price record) ++
      encode_uint 8 (orig_volume_fractional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cancel_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (orig_trade_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (orig_tt_exempt_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (orig_trcond_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (orig_ssday_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (orig_side_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (orig_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (orig_volume_fractional_value, bytes) =>
                                                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; cancel_type := cancel_type_value; orig_trade_id := orig_trade_id_value; orig_tt_exempt := orig_tt_exempt_value; orig_trcond := orig_trcond_value; orig_ssday := orig_ssday_value; orig_side := orig_side_value; orig_price := orig_price_value; orig_volume_fractional := orig_volume_fractional_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalTradeCancelErrorMessage.

  Module FractionalTradeCorrectionMessage.

    (** Fractional Trade Correction Message (TP). *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      trade_id : N;
      orig_trade_id : N;
      orig_tt_exempt : list byte;
      orig_trcond : list byte;
      orig_ssday : N;
      side : list byte;
      orig_price : N;
      orig_volume_fractional : N;
      new_tt_exempt : list byte;
      new_trcond : list byte;
      new_ssday : N;
      new_price : N;
      new_volume_fractional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (orig_trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (orig_tt_exempt record) = 1 /\
      Datatypes.length (orig_trcond record) = 4 /\
      (orig_ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (orig_price record < 256 ^ N.of_nat 8)%N /\
      (orig_volume_fractional record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (new_tt_exempt record) = 1 /\
      Datatypes.length (new_trcond record) = 4 /\
      (new_ssday record < 256 ^ N.of_nat 2)%N /\
      (new_price record < 256 ^ N.of_nat 8)%N /\
      (new_volume_fractional record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (orig_trade_id record) ++
      encode_bytes 1 (orig_tt_exempt record) ++
      encode_bytes 4 (orig_trcond record) ++
      encode_uint 2 (orig_ssday record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (orig_price record) ++
      encode_uint 8 (orig_volume_fractional record) ++
      encode_bytes 1 (new_tt_exempt record) ++
      encode_bytes 4 (new_trcond record) ++
      encode_uint 2 (new_ssday record) ++
      encode_uint 8 (new_price record) ++
      encode_uint 8 (new_volume_fractional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_2_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trade_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (orig_trade_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (orig_tt_exempt_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (orig_trcond_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (orig_ssday_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (side_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (orig_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (orig_volume_fractional_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (new_tt_exempt_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (new_trcond_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (new_ssday_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (new_price_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (new_volume_fractional_value, bytes) =>
                                                                                  Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; trade_id := trade_id_value; orig_trade_id := orig_trade_id_value; orig_tt_exempt := orig_tt_exempt_value; orig_trcond := orig_trcond_value; orig_ssday := orig_ssday_value; side := side_value; orig_price := orig_price_value; orig_volume_fractional := orig_volume_fractional_value; new_tt_exempt := new_tt_exempt_value; new_trcond := new_trcond_value; new_ssday := new_ssday_value; new_price := new_price_value; new_volume_fractional := new_volume_fractional_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalTradeCorrectionMessage.

  Module FractionalAsOfTradeReportMessage.

    (** Fractional As/Of Trade Report Message (TQ). *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      trade_id : N;
      tt_exempt : list byte;
      trcond : list byte;
      ssday : N;
      side : list byte;
      price : N;
      volume_fractional : N;
      trade_time : N;
      reversal : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (tt_exempt record) = 1 /\
      Datatypes.length (trcond record) = 4 /\
      (ssday record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (volume_fractional record < 256 ^ N.of_nat 8)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reversal record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trade_id record) ++
      encode_bytes 1 (tt_exempt record) ++
      encode_bytes 4 (trcond record) ++
      encode_uint 2 (ssday record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (volume_fractional record) ++
      encode_uint 8 (trade_time record) ++
      encode_bytes 1 (reversal record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (tt_exempt_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (trcond_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ssday_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (side_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (volume_fractional_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (trade_time_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (reversal_value, bytes) =>
                                                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; trade_id := trade_id_value; tt_exempt := tt_exempt_value; trcond := trcond_value; ssday := ssday_value; side := side_value; price := price_value; volume_fractional := volume_fractional_value; trade_time := trade_time_value; reversal := reversal_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalAsOfTradeReportMessage.

  Module TradingActionMessage.

    (** Trading Action Message (AO). Listing market notifies SIP of halts and other trading state events. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      action : list byte;
      action_sequence : N;
      action_time : N;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (action record) = 1 /\
      (action_sequence record < 256 ^ N.of_nat 4)%N /\
      (action_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reason record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (action record) ++
      encode_uint 4 (action_sequence record) ++
      encode_uint 8 (action_time record) ++
      encode_bytes 6 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (action_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (action_sequence_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (action_time_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (reason_value, bytes) =>
                                          Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; action := action_value; action_sequence := action_sequence_value; action_time := action_time_value; reason := reason_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingActionMessage.

  Module MarketCenterTradingActionMessage.

    (** Market Center Trading Action Message (AJ). Participant-specific trading halt on the participant's own market only. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      action : list byte;
      action_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (action record) = 1 /\
      (action_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (action record) ++
      encode_uint 8 (action_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (action_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (action_time_value, bytes) =>
                                  Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; action := action_value; action_time := action_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketCenterTradingActionMessage.

  Module MarketCenterMassTradingActionMessage.

    (** Market Center Mass Trading Action Message (AU). Applies action across a range of securities. No acknowledgement is returned. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      first_security : list byte;
      last_security : list byte;
      action : list byte;
      action_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (first_security record) = 11 /\
      Datatypes.length (last_security record) = 11 /\
      Datatypes.length (action record) = 1 /\
      (action_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (first_security record) ++
      encode_bytes 11 (last_security record) ++
      encode_bytes 1 (action record) ++
      encode_uint 8 (action_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (first_security_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (last_security_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (action_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (action_time_value, bytes) =>
                                      Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; first_security := first_security_value; last_security := last_security_value; action := action_value; action_time := action_time_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketCenterMassTradingActionMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Reg SHO Short Sale Price Test Restricted Indicator Message (AV). Notifies that a security has breached the short sale price test threshold. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (action_value, bytes) =>
                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; action := action_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module OpeningReferenceMidpointPriceMessage.

    (** Opening Reference Midpoint Price Message (AM). Listing market provides midpoint reference price for LULD calculations. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; price := price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningReferenceMidpointPriceMessage.

  Module T1AdjustedClosingPriceMessage.

    (** T1 Adjusted Closing Price Message (AN). Listing market provides closing price for LULD calculations. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; price := price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End T1AdjustedClosingPriceMessage.

  Module MarketOpenMessage.

    (** Market Open Message (AX). Indicates participant quotes should be marked as opened. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketOpenMessage.

  Module MarketClosedMessage.

    (** Market Closed Message (AY). Indicates the trading session is ready to close. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketClosedMessage.

  Module AuctionCollarMessage.

    (** Auction Collar Message (AE). Listing market provides new Price Protection Limits used during LULD trading pauses (and during extended operational hours). *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
      action_sequence : N;
      collar_reference_price : N;
      collar_up_price : N;
      collar_down_price : N;
      collar_extension : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (action_sequence record < 256 ^ N.of_nat 4)%N /\
      (collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (collar_up_price record < 256 ^ N.of_nat 8)%N /\
      (collar_down_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (collar_extension record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (action_sequence record) ++
      encode_uint 8 (collar_reference_price record) ++
      encode_uint 8 (collar_up_price record) ++
      encode_uint 8 (collar_down_price record) ++
      encode_bytes 1 (collar_extension record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (action_sequence_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (collar_reference_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (collar_up_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (collar_down_price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (collar_extension_value, bytes) =>
                                              Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value; action_sequence := action_sequence_value; collar_reference_price := collar_reference_price_value; collar_up_price := collar_up_price_value; collar_down_price := collar_down_price_value; collar_extension := collar_extension_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionCollarMessage.

  Module SequenceInquiryMessage.

    (** Sequence Inquiry Message (CC). Participant requests current expected sequence number from SIP. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SequenceInquiryMessage.

  Module SymbolStateInquiryMessage.

    (** Symbol State Inquiry Message (CS). Participant requests current per-symbol state from SIP. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
      symbol_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 11 (symbol_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value; symbol_long := symbol_long_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolStateInquiryMessage.

  Module EndOfParticipantReportingMessage.

    (** End Of Participant Reporting Message (CG). Participant signals it has finished reporting for the session. *)
    Record t := {
      orig : list byte;
      timestamp_1 : N;
      feed_sequence : N;
      part_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      Some ({| orig := orig_value; timestamp_1 := timestamp_1_value; feed_sequence := feed_sequence_value; part_token := part_token_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfParticipantReportingMessage.

  Module ReturnMarketCenterTradingActionAcknowledgementMessage.

    (** Market Center Trading Action Acknowledgement Message (aJ). Acknowledges a Market Center Trading Action (AJ). *)
    Record t := {
      orig : list byte;
      sip_time : N;
      symbol_long : list byte;
      action : list byte;
      action_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (action record) = 1 /\
      (action_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (action record) ++
      encode_uint 8 (action_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (symbol_long_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (action_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (action_time_value, bytes) =>
                          Some ({| orig := orig_value; sip_time := sip_time_value; symbol_long := symbol_long_value; action := action_value; action_time := action_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReturnMarketCenterTradingActionAcknowledgementMessage.

  Module ReturnMarketOpenMessage.

    (** Return Market Open Message (aX). SIP confirms market is open. *)
    Record t := {
      orig : list byte;
      sip_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              Some ({| orig := orig_value; sip_time := sip_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End ReturnMarketOpenMessage.

  Module ReturnMarketClosedMessage.

    (** Return Market Closed Message (aY). SIP confirms market is closed. *)
    Record t := {
      orig : list byte;
      sip_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              Some ({| orig := orig_value; sip_time := sip_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End ReturnMarketClosedMessage.

  Module RejectMessage.

    (** Reject Message (aR). SIP returns this message when an inbound message is rejected. syntaxViolation 'Y' indicates a syntax error and the port will be disconnected. *)
    Record t := {
      orig : list byte;
      sip_time : N;
      feed_sequence : N;
      part_token : N;
      reject_code : N;
      syntax_violation : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (reject_code record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (syntax_violation record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 2 (reject_code record) ++
      encode_bytes 1 (syntax_violation record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (reject_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (syntax_violation_value, bytes) =>
                              Some ({| orig := orig_value; sip_time := sip_time_value; feed_sequence := feed_sequence_value; part_token := part_token_value; reject_code := reject_code_value; syntax_violation := syntax_violation_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End RejectMessage.

  Module SequenceAcknowledgementMessage.

    (** Sequence Acknowledgement Message (aK). SIP positively acknowledges receipt of an inbound message when the port is configured for acknowledgements. *)
    Record t := {
      orig : list byte;
      sip_time : N;
      feed_sequence : N;
      part_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      Some ({| orig := orig_value; sip_time := sip_time_value; feed_sequence := feed_sequence_value; part_token := part_token_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SequenceAcknowledgementMessage.

  Module ParticipantInputWarningMessage.

    (** Participant Input Warning Message (aW). Sent when an inbound quote message would exceed odd-lot price-level limits. Carries the unprocessed price levels as attachments whose form is selected by olAttachmenType (2=Short, 3=Long, 5=ADF MPID). The attached price levels are not enumerated as Pdf.xml groups in this version — extend in a follow-up release when the loader's value-gated Optional rules are wired through Edits.xml. *)
    Record t := {
      orig : list byte;
      sip_time : N;
      feed_sequence : N;
      part_token : N;
      warning_code : N;
      symbol_long : list byte;
      ol_attachmen_type : list byte;
      ol_attachment_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      (warning_code record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (ol_attachmen_type record) = 1 /\
      (ol_attachment_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_uint 2 (warning_code record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (ol_attachmen_type record) ++
      encode_uint 2 (ol_attachment_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (warning_code_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (ol_attachmen_type_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ol_attachment_count_value, bytes) =>
                                      Some ({| orig := orig_value; sip_time := sip_time_value; feed_sequence := feed_sequence_value; part_token := part_token_value; warning_code := warning_code_value; symbol_long := symbol_long_value; ol_attachmen_type := ol_attachmen_type_value; ol_attachment_count := ol_attachment_count_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantInputWarningMessage.

  Module StartOfDayMessage.

    (** Start Of Day Message (cE). SIP signals it is open and ready to receive messages from participants. *)
    Record t := {
      orig : list byte;
      sip_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              Some ({| orig := orig_value; sip_time := sip_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End StartOfDayMessage.

  Module EndOfDayMessage.

    (** End Of Day Message (cF). SIP signals it has no further data or control messages for the day and is shutting down. *)
    Record t := {
      orig : list byte;
      sip_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              Some ({| orig := orig_value; sip_time := sip_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End EndOfDayMessage.

  Module SequenceInquiryResponseMessage.

    (** Sequence Inquiry Response Message (cC). Sent unsequenced in response to a CC inquiry. Carries the next expected feedSequence, last partToken received, and the present SIP state. *)
    Record t := {
      orig : list byte;
      sip_time : N;
      feed_sequence : N;
      part_token : N;
      sip_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N /\
      (feed_sequence record < 256 ^ N.of_nat 8)%N /\
      (part_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sip_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record) ++
      encode_uint 8 (feed_sequence record) ++
      encode_uint 8 (part_token record) ++
      encode_bytes 1 (sip_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (feed_sequence_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (part_token_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (sip_state_value, bytes) =>
                          Some ({| orig := orig_value; sip_time := sip_time_value; feed_sequence := feed_sequence_value; part_token := part_token_value; sip_state := sip_state_value |}, bytes)
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SequenceInquiryResponseMessage.

  Module SymbolStateInquiryResponseMessage.

    (** Symbol State Inquiry Response Message (cS). Sent unsequenced in response to a CS inquiry. Carries next expected tradeId, next actionSequence, and the symbolState. *)
    Record t := {
      orig : list byte;
      sip_time : N;
      symbol_long : list byte;
      next_trade_id : N;
      next_action_sequence : N;
      symbol_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (orig record) = 2 /\
      (sip_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (next_trade_id record < 256 ^ N.of_nat 4)%N /\
      (next_action_sequence record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (orig record) ++
      encode_uint 8 (sip_time record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (next_trade_id record) ++
      encode_uint 4 (next_action_sequence record) ++
      encode_bytes 1 (symbol_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (orig_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sip_time_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (symbol_long_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (next_trade_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (next_action_sequence_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (symbol_state_value, bytes) =>
                              Some ({| orig := orig_value; sip_time := sip_time_value; symbol_long := symbol_long_value; next_trade_id := next_trade_id_value; next_action_sequence := next_action_sequence_value; symbol_state := symbol_state_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolStateInquiryResponseMessage.

  Module LoginRequestPacket.

    (** SoupBinTCP Login Request Packet sent by the client to begin a session *)
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
      Datatypes.length (requested_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 20 (requested_sequence_number record).

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
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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

End NasdaqUtpInputV40Client.
