From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Output

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
      - the dispatch that chooses a message by its type
      - a field present only on a condition
      - a length prefix framing what follows
  *)

Module NasdaqUqdfOutputV15.

  Module PacketHeader.

    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End PacketHeader.

  Module MessageHeader.

    (** Mold Udp Message Header *)
    Record t := {
      message_length : N;
      version : N;
      message_category : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_category record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (version record) ++
      encode_bytes 1 (message_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (version_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_category_value, bytes) =>
                  Some ({| message_length := message_length_value; version := version_value; message_category := message_category_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  Module MessageInfo.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo.

  Module MessageInfo2.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo2.

  Module MessageInfo3.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo3.

  Module FinraAdfMarketParticipantQuotationMessage.

    (** For FINRA quotes that do not affect the NBBO or FINRA BBO a FINRA ADF Market Participant Quotation Message will be sent. *)
    Record t := {
      message_info : MessageInfo3.t;
      finra_timestamp : N;
      symbol_long : list byte;
      bid_price : N;
      bid_size : N;
      ask_price : N;
      ask_size : N;
      quote_condition : list byte;
      finra_market_participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo3.bounded (message_info record) /\
      (finra_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 8)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      Datatypes.length (finra_market_participant record) = 4.

    Definition encode (record : t) : list byte :=
      MessageInfo3.encode (message_info record) ++
      encode_uint 8 (finra_timestamp record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 8 (bid_price record) ++
      encode_uint 4 (bid_size record) ++
      encode_uint 8 (ask_price record) ++
      encode_uint 4 (ask_size record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_bytes 4 (finra_market_participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo3.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (finra_timestamp_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (symbol_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_size_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ask_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (ask_size_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (quote_condition_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (finra_market_participant_value, bytes) =>
                                          Some ({| message_info := message_info_value; finra_timestamp := finra_timestamp_value; symbol_long := symbol_long_value; bid_price := bid_price_value; bid_size := bid_size_value; ask_price := ask_price_value; ask_size := ask_size_value; quote_condition := quote_condition_value; finra_market_participant := finra_market_participant_value |}, bytes)
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
      rewrite !length_app, !MessageInfo3.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo3.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo3.eq_dec]. Defined.

  End FinraAdfMarketParticipantQuotationMessage.

  Module MessageInfo4.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo4.

  Module MessageInfo5.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo5.

  Module CrossSroTradingActionMessage.

    (** This fixed format message will be used to inform subscribers of trading actions – such as halts, pauses, quotation resumptions and trading resumptions *)
    Record t := {
      message_info : MessageInfo5.t;
      symbol_long : list byte;
      trading_action_code : list byte;
      trading_action_sequence_number : N;
      action_timestamp : N;
      trading_action_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo5.bounded (message_info record) /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (trading_action_code record) = 1 /\
      (trading_action_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (action_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_action_reason record) = 6.

    Definition encode (record : t) : list byte :=
      MessageInfo5.encode (message_info record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (trading_action_code record) ++
      encode_uint 4 (trading_action_sequence_number record) ++
      encode_uint 8 (action_timestamp record) ++
      encode_bytes 6 (trading_action_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo5.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_action_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trading_action_sequence_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (action_timestamp_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (trading_action_reason_value, bytes) =>
                              Some ({| message_info := message_info_value; symbol_long := symbol_long_value; trading_action_code := trading_action_code_value; trading_action_sequence_number := trading_action_sequence_number_value; action_timestamp := action_timestamp_value; trading_action_reason := trading_action_reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageInfo5.encode_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo5.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo5.eq_dec]. Defined.

  End CrossSroTradingActionMessage.

  Module MessageInfo6.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo6.

  Module MarketCenterTradingActionMessage.

    (** This fixed format message will inform UTP data feed subscribers of when a UTP participant invokes or releases a market center-specific trading halt for a NASDAQ-listed security. *)
    Record t := {
      message_info : MessageInfo6.t;
      symbol_long : list byte;
      trading_action_code : list byte;
      action_timestamp : N;
      market_center_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo6.bounded (message_info record) /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (trading_action_code record) = 1 /\
      (action_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_center_identifier record) = 1.

    Definition encode (record : t) : list byte :=
      MessageInfo6.encode (message_info record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (trading_action_code record) ++
      encode_uint 8 (action_timestamp record) ++
      encode_bytes 1 (market_center_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo6.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_action_code_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (action_timestamp_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (market_center_identifier_value, bytes) =>
                          Some ({| message_info := message_info_value; symbol_long := symbol_long_value; trading_action_code := trading_action_code_value; action_timestamp := action_timestamp_value; market_center_identifier := market_center_identifier_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageInfo6.encode_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo6.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo6.eq_dec]. Defined.

  End MarketCenterTradingActionMessage.

  Module MessageInfo7.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo7.

  Module IssueSymbolDirectoryMessage.

    (** General Administrative *)
    Record t := {
      message_info : MessageInfo7.t;
      symbol_long : list byte;
      old_symbol : list byte;
      issue_name : list byte;
      issue_type : list byte;
      issue_subtype : list byte;
      market_tier : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      round_lot_size : N;
      financial_status_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo7.bounded (message_info record) /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (old_symbol record) = 11 /\
      Datatypes.length (issue_name record) = 30 /\
      Datatypes.length (issue_type record) = 1 /\
      Datatypes.length (issue_subtype record) = 2 /\
      Datatypes.length (market_tier record) = 1 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (financial_status_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      MessageInfo7.encode (message_info record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 11 (old_symbol record) ++
      encode_bytes 30 (issue_name record) ++
      encode_bytes 1 (issue_type record) ++
      encode_bytes 2 (issue_subtype record) ++
      encode_bytes 1 (market_tier record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_uint 2 (round_lot_size record) ++
      encode_bytes 1 (financial_status_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo7.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (old_symbol_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (issue_name_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (issue_type_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (issue_subtype_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (market_tier_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (authenticity_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (short_sale_threshold_indicator_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (round_lot_size_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (financial_status_indicator_value, bytes) =>
                                                  Some ({| message_info := message_info_value; symbol_long := symbol_long_value; old_symbol := old_symbol_value; issue_name := issue_name_value; issue_type := issue_type_value; issue_subtype := issue_subtype_value; market_tier := market_tier_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; round_lot_size := round_lot_size_value; financial_status_indicator := financial_status_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 87.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageInfo7.encode_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo7.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo7.eq_dec]. Defined.

  End IssueSymbolDirectoryMessage.

  Module MessageInfo8.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo8.

  Module RegulationShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Used to disseminate quotation data for NASDAQ listed securities *)
    Record t := {
      message_info : MessageInfo8.t;
      symbol_short : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo8.bounded (message_info record) /\
      Datatypes.length (symbol_short record) = 5 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      MessageInfo8.encode (message_info record) ++
      encode_bytes 5 (symbol_short record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo8.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reg_sho_action_value, bytes) =>
                  Some ({| message_info := message_info_value; symbol_short := symbol_short_value; reg_sho_action := reg_sho_action_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageInfo8.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo8.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo8.eq_dec]. Defined.

  End RegulationShoShortSalePriceTestRestrictedIndicatorMessage.

  Module MessageInfo9.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo9.

  Module LimitUpLimitDownPriceBandMessage.

    (** Designed to prevent trades in individual NMS Stocks from occurring outside of specified Upper and Lower Limit Price Bands *)
    Record t := {
      message_info : MessageInfo9.t;
      symbol_long : list byte;
      luld_price_band_indicator : list byte;
      luld_timestamp : N;
      limit_down_price : N;
      limit_up_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo9.bounded (message_info record) /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (luld_price_band_indicator record) = 1 /\
      (luld_timestamp record < 256 ^ N.of_nat 8)%N /\
      (limit_down_price record < 256 ^ N.of_nat 8)%N /\
      (limit_up_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      MessageInfo9.encode (message_info record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (luld_price_band_indicator record) ++
      encode_uint 8 (luld_timestamp record) ++
      encode_uint 8 (limit_down_price record) ++
      encode_uint 8 (limit_up_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo9.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (luld_price_band_indicator_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (luld_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (limit_down_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (limit_up_price_value, bytes) =>
                              Some ({| message_info := message_info_value; symbol_long := symbol_long_value; luld_price_band_indicator := luld_price_band_indicator_value; luld_timestamp := luld_timestamp_value; limit_down_price := limit_down_price_value; limit_up_price := limit_up_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageInfo9.encode_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo9.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo9.eq_dec]. Defined.

  End LimitUpLimitDownPriceBandMessage.

  Module MessageInfo10.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo10.

  Module MarketWideCircuitBreakerDeclineLevelMessage.

    (** A Market Wide Circuit Breaker (MWCB) Level message will inform participants and the UTP data recipients what the daily MWCB breach points are set to for the current trading day *)
    Record t := {
      message_info : MessageInfo10.t;
      mwcb_level_1 : N;
      mwcb_level_2 : N;
      mwcb_level_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo10.bounded (message_info record) /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      MessageInfo10.encode (message_info record) ++
      encode_uint 8 (mwcb_level_1 record) ++
      encode_uint 8 (mwcb_level_2 record) ++
      encode_uint 8 (mwcb_level_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo10.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (mwcb_level_1_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (mwcb_level_2_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (mwcb_level_3_value, bytes) =>
                      Some ({| message_info := message_info_value; mwcb_level_1 := mwcb_level_1_value; mwcb_level_2 := mwcb_level_2_value; mwcb_level_3 := mwcb_level_3_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageInfo10.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo10.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageInfo10.eq_dec]. Defined.

  End MarketWideCircuitBreakerDeclineLevelMessage.

  Module MessageInfo11.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo11.

  Module MarketWideCircuitBreakerStatusMessage.

    (** A Market Wide Circuit Breaker (MWCB) Status message will inform participants and the UTP data recipients when a MWCB has breached one of the established levels. *)
    Record t := {
      message_info : MessageInfo11.t;
      mwcb_status_level_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo11.bounded (message_info record) /\
      Datatypes.length (mwcb_status_level_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      MessageInfo11.encode (message_info record) ++
      encode_bytes 1 (mwcb_status_level_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo11.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (mwcb_status_level_indicator_value, bytes) =>
              Some ({| message_info := message_info_value; mwcb_status_level_indicator := mwcb_status_level_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !MessageInfo11.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo11.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo11.eq_dec]. Defined.

  End MarketWideCircuitBreakerStatusMessage.

  Module MessageInfo12.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo12.

  Module AuctionCollarMessage.

    (** Primary markets using an automated reopening will calculate new Auction Collars, in compliance with rules around prices for re-opening, when applicable and publish this new Auction Collar Message *)
    Record t := {
      message_info : MessageInfo12.t;
      symbol_long : list byte;
      trading_action_sequence_number : N;
      collar_reference_price : N;
      collar_up_price : N;
      collar_down_price : N;
      collar_extension_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo12.bounded (message_info record) /\
      Datatypes.length (symbol_long record) = 11 /\
      (trading_action_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (collar_up_price record < 256 ^ N.of_nat 8)%N /\
      (collar_down_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (collar_extension_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      MessageInfo12.encode (message_info record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trading_action_sequence_number record) ++
      encode_uint 8 (collar_reference_price record) ++
      encode_uint 8 (collar_up_price record) ++
      encode_uint 8 (collar_down_price record) ++
      encode_bytes 1 (collar_extension_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo12.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trading_action_sequence_number_value, bytes) =>
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
                              | Some (collar_extension_indicator_value, bytes) =>
                                  Some ({| message_info := message_info_value; symbol_long := symbol_long_value; trading_action_sequence_number := trading_action_sequence_number_value; collar_reference_price := collar_reference_price_value; collar_up_price := collar_up_price_value; collar_down_price := collar_down_price_value; collar_extension_indicator := collar_extension_indicator_value |}, bytes)
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
      rewrite !length_app, !MessageInfo12.encode_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite MessageInfo12.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply MessageInfo12.eq_dec]. Defined.

  End AuctionCollarMessage.

  Module MessageInfo13.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo13.

  Module MessageInfo14.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo14.

  Module StartOfDayMessage.

    (** The Start of Day control message signifies the beginning of each operational cycle for SIP Processing *)
    Record t := {
      message_info : MessageInfo14.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo14.bounded (message_info record).

    Definition encode (record : t) : list byte :=
      MessageInfo14.encode (message_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo14.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          Some ({| message_info := message_info_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !MessageInfo14.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageInfo14.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageInfo14.eq_dec]. Defined.

  End StartOfDayMessage.

  Module MessageInfo15.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo15.

  Module EndOfDayMessage.

    (** The End of Day control message signals the end of active message dissemination for the UTP SIP operational cycle *)
    Record t := {
      message_info : MessageInfo15.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo15.bounded (message_info record).

    Definition encode (record : t) : list byte :=
      MessageInfo15.encode (message_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo15.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          Some ({| message_info := message_info_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !MessageInfo15.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageInfo15.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageInfo15.eq_dec]. Defined.

  End EndOfDayMessage.

  Module MessageInfo16.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo16.

  Module MarketSessionOpenMessage.

    (** The Market Session Open Control Message signifies the opening of market systems for the session indicated in the Message Header *)
    Record t := {
      message_info : MessageInfo16.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo16.bounded (message_info record).

    Definition encode (record : t) : list byte :=
      MessageInfo16.encode (message_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo16.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          Some ({| message_info := message_info_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !MessageInfo16.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageInfo16.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageInfo16.eq_dec]. Defined.

  End MarketSessionOpenMessage.

  Module MessageInfo17.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo17.

  Module MarketSessionCloseMessage.

    (** The Session Close Control Message signals the closing of market systems for the session indicated in the Message Header *)
    Record t := {
      message_info : MessageInfo17.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo17.bounded (message_info record).

    Definition encode (record : t) : list byte :=
      MessageInfo17.encode (message_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo17.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          Some ({| message_info := message_info_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !MessageInfo17.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageInfo17.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageInfo17.eq_dec]. Defined.

  End MarketSessionCloseMessage.

  Module MessageInfo18.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo18.

  Module EndOfTransmissionsMessage.

    (** The End of Transmissions Message signals that there will be no further transmissions of data sent through the UTP SIP line *)
    Record t := {
      message_info : MessageInfo18.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo18.bounded (message_info record).

    Definition encode (record : t) : list byte :=
      MessageInfo18.encode (message_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo18.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          Some ({| message_info := message_info_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !MessageInfo18.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageInfo18.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageInfo18.eq_dec]. Defined.

  End EndOfTransmissionsMessage.

  Module MessageInfo19.

    (** Message Info *)
    Record t := {
      market_center_originator_id : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      participant_timestamp : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator_id record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_timestamp record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator_id record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (participant_timestamp record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (participant_timestamp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator_id := market_center_originator_id_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; participant_timestamp := participant_timestamp_value; participant_token := participant_token_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageInfo19.

  Module QuoteWipeOutMessage.

    (** The Quote Wipe-Out message will be sent to indicate that a UTP Participant is experiencing a problem with their internal systems and, as a result, are not able to update their UTP BBO quotation information *)
    Record t := {
      message_info : MessageInfo19.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      MessageInfo19.bounded (message_info record).

    Definition encode (record : t) : list byte :=
      MessageInfo19.encode (message_info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match MessageInfo19.decode bytes with
      | None => None
      | Some (message_info_value, bytes) =>
          Some ({| message_info := message_info_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !MessageInfo19.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite MessageInfo19.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply MessageInfo19.eq_dec]. Defined.

  End QuoteWipeOutMessage.

End NasdaqUqdfOutputV15.
