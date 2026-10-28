From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Drop

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

Module PsxEquitiesDropV22Server.

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

    (** Time Stamp and Type opening every Drop message line *)
    Record t := {
      time_stamp : list byte;
      comma : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (time_stamp record) = 9 /\
      Datatypes.length (comma record) = 1 /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (time_stamp record) ++
      encode_bytes 1 (comma record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (time_stamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (comma_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_type_value, bytes) =>
                  Some ({| time_stamp := time_stamp_value; comma := comma_value; message_type := message_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SequencedMessageHeader.

  Module NewOrderAcceptedMessage.

    (** New order accepted. *)
    Record t := {
      separator_1 : N;
      source : list byte;
      separator_2 : N;
      user : list byte;
      separator_3 : N;
      token : list byte;
      separator_4 : N;
      replaced_token : list byte;
      separator_5 : N;
      buy_sell : list byte;
      separator_6 : N;
      shares : list byte;
      separator_7 : N;
      stock : list byte;
      separator_8 : N;
      price : list byte;
      separator_9 : N;
      firm : list byte;
      separator_10 : N;
      reference : list byte;
      separator_11 : N;
      match_number : list byte;
      separator_12 : N;
      capacity : list byte;
      separator_13 : N;
      liquidity_code : list byte;
      separator_14 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (source record) = 6 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (replaced_token record) = 10 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 6 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 8 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 11 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 12 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (match_number record) = 12 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_13 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_14 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (separator_1 record) ++
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 10 (replaced_token record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 6 (shares record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 11 (price record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 12 (reference record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 12 (match_number record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_13 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_14 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (separator_1_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (source_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (separator_2_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (user_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (separator_3_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (token_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (separator_4_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (replaced_token_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (separator_5_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (buy_sell_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (separator_6_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (shares_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (separator_7_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (stock_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (separator_8_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (separator_9_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (firm_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (separator_10_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (reference_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (separator_11_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (match_number_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (separator_12_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (capacity_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (separator_13_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (liquidity_code_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (separator_14_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (clearing_code_value, bytes) =>
                                                                                                                      Some ({| separator_1 := separator_1_value; source := source_value; separator_2 := separator_2_value; user := user_value; separator_3 := separator_3_value; token := token_value; separator_4 := separator_4_value; replaced_token := replaced_token_value; separator_5 := separator_5_value; buy_sell := buy_sell_value; separator_6 := separator_6_value; shares := shares_value; separator_7 := separator_7_value; stock := stock_value; separator_8 := separator_8_value; price := price_value; separator_9 := separator_9_value; firm := firm_value; separator_10 := separator_10_value; reference := reference_value; separator_11 := separator_11_value; match_number := match_number_value; separator_12 := separator_12_value; capacity := capacity_value; separator_13 := separator_13_value; liquidity_code := liquidity_code_value; separator_14 := separator_14_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderAcceptedMessage.

  Module ExistingOrderExecutedMessage.

    (** Existing order executed. *)
    Record t := {
      separator_1 : N;
      source : list byte;
      separator_2 : N;
      user : list byte;
      separator_3 : N;
      token : list byte;
      separator_4 : N;
      replaced_token : list byte;
      separator_5 : N;
      buy_sell : list byte;
      separator_6 : N;
      shares : list byte;
      separator_7 : N;
      stock : list byte;
      separator_8 : N;
      price : list byte;
      separator_9 : N;
      firm : list byte;
      separator_10 : N;
      reference : list byte;
      separator_11 : N;
      match_number : list byte;
      separator_12 : N;
      capacity : list byte;
      separator_13 : N;
      liquidity_code : list byte;
      separator_14 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (source record) = 6 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (replaced_token record) = 10 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 6 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 8 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 11 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 12 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (match_number record) = 12 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_13 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_14 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (separator_1 record) ++
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 10 (replaced_token record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 6 (shares record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 11 (price record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 12 (reference record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 12 (match_number record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_13 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_14 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (separator_1_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (source_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (separator_2_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (user_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (separator_3_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (token_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (separator_4_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (replaced_token_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (separator_5_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (buy_sell_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (separator_6_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (shares_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (separator_7_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (stock_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (separator_8_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (separator_9_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (firm_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (separator_10_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (reference_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (separator_11_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (match_number_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (separator_12_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (capacity_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (separator_13_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (liquidity_code_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (separator_14_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (clearing_code_value, bytes) =>
                                                                                                                      Some ({| separator_1 := separator_1_value; source := source_value; separator_2 := separator_2_value; user := user_value; separator_3 := separator_3_value; token := token_value; separator_4 := separator_4_value; replaced_token := replaced_token_value; separator_5 := separator_5_value; buy_sell := buy_sell_value; separator_6 := separator_6_value; shares := shares_value; separator_7 := separator_7_value; stock := stock_value; separator_8 := separator_8_value; price := price_value; separator_9 := separator_9_value; firm := firm_value; separator_10 := separator_10_value; reference := reference_value; separator_11 := separator_11_value; match_number := match_number_value; separator_12 := separator_12_value; capacity := capacity_value; separator_13 := separator_13_value; liquidity_code := liquidity_code_value; separator_14 := separator_14_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExistingOrderExecutedMessage.

  Module ExistingOrderCanceledMessage.

    (** Existing order canceled. *)
    Record t := {
      separator_1 : N;
      source : list byte;
      separator_2 : N;
      user : list byte;
      separator_3 : N;
      token : list byte;
      separator_4 : N;
      replaced_token : list byte;
      separator_5 : N;
      buy_sell : list byte;
      separator_6 : N;
      shares : list byte;
      separator_7 : N;
      stock : list byte;
      separator_8 : N;
      price : list byte;
      separator_9 : N;
      firm : list byte;
      separator_10 : N;
      reference : list byte;
      separator_11 : N;
      match_number : list byte;
      separator_12 : N;
      capacity : list byte;
      separator_13 : N;
      liquidity_code : list byte;
      separator_14 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (source record) = 6 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (replaced_token record) = 10 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 6 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 8 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 11 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 12 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (match_number record) = 12 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_13 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_14 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (separator_1 record) ++
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 10 (replaced_token record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 6 (shares record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 11 (price record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 12 (reference record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 12 (match_number record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_13 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_14 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (separator_1_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (source_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (separator_2_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (user_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (separator_3_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (token_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (separator_4_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (replaced_token_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (separator_5_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (buy_sell_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (separator_6_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (shares_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (separator_7_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (stock_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (separator_8_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (separator_9_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (firm_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (separator_10_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (reference_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (separator_11_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (match_number_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (separator_12_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (capacity_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (separator_13_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (liquidity_code_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (separator_14_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (clearing_code_value, bytes) =>
                                                                                                                      Some ({| separator_1 := separator_1_value; source := source_value; separator_2 := separator_2_value; user := user_value; separator_3 := separator_3_value; token := token_value; separator_4 := separator_4_value; replaced_token := replaced_token_value; separator_5 := separator_5_value; buy_sell := buy_sell_value; separator_6 := separator_6_value; shares := shares_value; separator_7 := separator_7_value; stock := stock_value; separator_8 := separator_8_value; price := price_value; separator_9 := separator_9_value; firm := firm_value; separator_10 := separator_10_value; reference := reference_value; separator_11 := separator_11_value; match_number := match_number_value; separator_12 := separator_12_value; capacity := capacity_value; separator_13 := separator_13_value; liquidity_code := liquidity_code_value; separator_14 := separator_14_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExistingOrderCanceledMessage.

  Module PreviousExecutionBrokenMessage.

    (** Previous execution broken. *)
    Record t := {
      separator_1 : N;
      source : list byte;
      separator_2 : N;
      user : list byte;
      separator_3 : N;
      token : list byte;
      separator_4 : N;
      replaced_token : list byte;
      separator_5 : N;
      buy_sell : list byte;
      separator_6 : N;
      shares : list byte;
      separator_7 : N;
      stock : list byte;
      separator_8 : N;
      price : list byte;
      separator_9 : N;
      firm : list byte;
      separator_10 : N;
      reference : list byte;
      separator_11 : N;
      match_number : list byte;
      separator_12 : N;
      capacity : list byte;
      separator_13 : N;
      liquidity_code : list byte;
      separator_14 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (source record) = 6 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (replaced_token record) = 10 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 6 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 8 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 11 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 12 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (match_number record) = 12 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_13 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_14 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (separator_1 record) ++
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 10 (replaced_token record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 6 (shares record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 11 (price record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 12 (reference record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 12 (match_number record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_13 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_14 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (separator_1_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (source_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (separator_2_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (user_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (separator_3_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (token_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (separator_4_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (replaced_token_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (separator_5_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (buy_sell_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (separator_6_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (shares_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (separator_7_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (stock_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (separator_8_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (separator_9_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (firm_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (separator_10_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (reference_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (separator_11_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (match_number_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (separator_12_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (capacity_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (separator_13_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (liquidity_code_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (separator_14_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (clearing_code_value, bytes) =>
                                                                                                                      Some ({| separator_1 := separator_1_value; source := source_value; separator_2 := separator_2_value; user := user_value; separator_3 := separator_3_value; token := token_value; separator_4 := separator_4_value; replaced_token := replaced_token_value; separator_5 := separator_5_value; buy_sell := buy_sell_value; separator_6 := separator_6_value; shares := shares_value; separator_7 := separator_7_value; stock := stock_value; separator_8 := separator_8_value; price := price_value; separator_9 := separator_9_value; firm := firm_value; separator_10 := separator_10_value; reference := reference_value; separator_11 := separator_11_value; match_number := match_number_value; separator_12 := separator_12_value; capacity := capacity_value; separator_13 := separator_13_value; liquidity_code := liquidity_code_value; separator_14 := separator_14_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousExecutionBrokenMessage.

  Module ExistingOrderReplacedMessage.

    (** Existing order replaced. *)
    Record t := {
      separator_1 : N;
      source : list byte;
      separator_2 : N;
      user : list byte;
      separator_3 : N;
      token : list byte;
      separator_4 : N;
      replaced_token : list byte;
      separator_5 : N;
      buy_sell : list byte;
      separator_6 : N;
      shares : list byte;
      separator_7 : N;
      stock : list byte;
      separator_8 : N;
      price : list byte;
      separator_9 : N;
      firm : list byte;
      separator_10 : N;
      reference : list byte;
      separator_11 : N;
      match_number : list byte;
      separator_12 : N;
      capacity : list byte;
      separator_13 : N;
      liquidity_code : list byte;
      separator_14 : N;
      clearing_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (separator_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (source record) = 6 /\
      (separator_2 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (user record) = 4 /\
      (separator_3 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (token record) = 10 /\
      (separator_4 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (replaced_token record) = 10 /\
      (separator_5 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (separator_6 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (shares record) = 6 /\
      (separator_7 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock record) = 8 /\
      (separator_8 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price record) = 11 /\
      (separator_9 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (firm record) = 4 /\
      (separator_10 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference record) = 12 /\
      (separator_11 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (match_number record) = 12 /\
      (separator_12 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (capacity record) = 1 /\
      (separator_13 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (liquidity_code record) = 1 /\
      (separator_14 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (separator_1 record) ++
      encode_bytes 6 (source record) ++
      encode_uint 1 (separator_2 record) ++
      encode_bytes 4 (user record) ++
      encode_uint 1 (separator_3 record) ++
      encode_bytes 10 (token record) ++
      encode_uint 1 (separator_4 record) ++
      encode_bytes 10 (replaced_token record) ++
      encode_uint 1 (separator_5 record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 1 (separator_6 record) ++
      encode_bytes 6 (shares record) ++
      encode_uint 1 (separator_7 record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 1 (separator_8 record) ++
      encode_bytes 11 (price record) ++
      encode_uint 1 (separator_9 record) ++
      encode_bytes 4 (firm record) ++
      encode_uint 1 (separator_10 record) ++
      encode_bytes 12 (reference record) ++
      encode_uint 1 (separator_11 record) ++
      encode_bytes 12 (match_number record) ++
      encode_uint 1 (separator_12 record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 1 (separator_13 record) ++
      encode_bytes 1 (liquidity_code record) ++
      encode_uint 1 (separator_14 record) ++
      encode_bytes 1 (clearing_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (separator_1_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (source_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (separator_2_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (user_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (separator_3_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (token_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (separator_4_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (replaced_token_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (separator_5_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (buy_sell_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (separator_6_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (shares_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (separator_7_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (stock_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (separator_8_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (price_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (separator_9_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (firm_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (separator_10_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (reference_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (separator_11_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (match_number_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (separator_12_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (capacity_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (separator_13_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (liquidity_code_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (separator_14_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (clearing_code_value, bytes) =>
                                                                                                                      Some ({| separator_1 := separator_1_value; source := source_value; separator_2 := separator_2_value; user := user_value; separator_3 := separator_3_value; token := token_value; separator_4 := separator_4_value; replaced_token := replaced_token_value; separator_5 := separator_5_value; buy_sell := buy_sell_value; separator_6 := separator_6_value; shares := shares_value; separator_7 := separator_7_value; stock := stock_value; separator_8 := separator_8_value; price := price_value; separator_9 := separator_9_value; firm := firm_value; separator_10 := separator_10_value; reference := reference_value; separator_11 := separator_11_value; match_number := match_number_value; separator_12 := separator_12_value; capacity := capacity_value; separator_13 := separator_13_value; liquidity_code := liquidity_code_value; separator_14 := separator_14_value; clearing_code := clearing_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExistingOrderReplacedMessage.

End PsxEquitiesDropV22Server.
