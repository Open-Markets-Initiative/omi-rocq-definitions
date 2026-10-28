From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Last Sale

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

Module BxeEquitiesLastSaleV15.

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

  Module LastSaleEuropeMessage.

    (** Last Sale Europe Messages are sent when an order on a Cboe order book is executed in whole or in part, or when a reported trade is submitted to Cboe *)
    Record t := {
      trading_date_time : list byte;
      symbol : list byte;
      price : list byte;
      price_currency : list byte;
      executed_shares : list byte;
      execution_venue : list byte;
      publication_date_time : list byte;
      trade_id : list byte;
      transaction_category : list byte;
      negotiation_flag : list byte;
      agency_cross_trade : list byte;
      modification_indicator : list byte;
      benchmark_reference_indicator : list byte;
      special_dividend : list byte;
      price_discovery_process : list byte;
      algorithmic_indicator : list byte;
      post_trade_deferral_reason : list byte;
      duplicative_indicator : list byte;
      jurisdiction : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_date_time record) = 27 /\
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (price record) = 18 /\
      Datatypes.length (price_currency record) = 3 /\
      Datatypes.length (executed_shares record) = 12 /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (publication_date_time record) = 27 /\
      Datatypes.length (trade_id record) = 12 /\
      Datatypes.length (transaction_category record) = 4 /\
      Datatypes.length (negotiation_flag record) = 4 /\
      Datatypes.length (agency_cross_trade record) = 4 /\
      Datatypes.length (modification_indicator record) = 4 /\
      Datatypes.length (benchmark_reference_indicator record) = 4 /\
      Datatypes.length (special_dividend record) = 4 /\
      Datatypes.length (price_discovery_process record) = 4 /\
      Datatypes.length (algorithmic_indicator record) = 4 /\
      Datatypes.length (post_trade_deferral_reason record) = 4 /\
      Datatypes.length (duplicative_indicator record) = 4 /\
      Datatypes.length (jurisdiction record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 27 (trading_date_time record) ++
      encode_bytes 12 (symbol record) ++
      encode_bytes 18 (price record) ++
      encode_bytes 3 (price_currency record) ++
      encode_bytes 12 (executed_shares record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 27 (publication_date_time record) ++
      encode_bytes 12 (trade_id record) ++
      encode_bytes 4 (transaction_category record) ++
      encode_bytes 4 (negotiation_flag record) ++
      encode_bytes 4 (agency_cross_trade record) ++
      encode_bytes 4 (modification_indicator record) ++
      encode_bytes 4 (benchmark_reference_indicator record) ++
      encode_bytes 4 (special_dividend record) ++
      encode_bytes 4 (price_discovery_process record) ++
      encode_bytes 4 (algorithmic_indicator record) ++
      encode_bytes 4 (post_trade_deferral_reason record) ++
      encode_bytes 4 (duplicative_indicator record) ++
      encode_bytes 2 (jurisdiction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 27 bytes with
      | None => None
      | Some (trading_date_time_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 18 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (price_currency_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (executed_shares_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (execution_venue_value, bytes) =>
                              match decode_bytes 27 bytes with
                              | None => None
                              | Some (publication_date_time_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (trade_id_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (transaction_category_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (negotiation_flag_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (agency_cross_trade_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (modification_indicator_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (benchmark_reference_indicator_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (special_dividend_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (price_discovery_process_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (algorithmic_indicator_value, bytes) =>
                                                                      match decode_bytes 4 bytes with
                                                                      | None => None
                                                                      | Some (post_trade_deferral_reason_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (duplicative_indicator_value, bytes) =>
                                                                              match decode_bytes 2 bytes with
                                                                              | None => None
                                                                              | Some (jurisdiction_value, bytes) =>
                                                                                  Some ({| trading_date_time := trading_date_time_value; symbol := symbol_value; price := price_value; price_currency := price_currency_value; executed_shares := executed_shares_value; execution_venue := execution_venue_value; publication_date_time := publication_date_time_value; trade_id := trade_id_value; transaction_category := transaction_category_value; negotiation_flag := negotiation_flag_value; agency_cross_trade := agency_cross_trade_value; modification_indicator := modification_indicator_value; benchmark_reference_indicator := benchmark_reference_indicator_value; special_dividend := special_dividend_value; price_discovery_process := price_discovery_process_value; algorithmic_indicator := algorithmic_indicator_value; post_trade_deferral_reason := post_trade_deferral_reason_value; duplicative_indicator := duplicative_indicator_value; jurisdiction := jurisdiction_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 157.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
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
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastSaleEuropeMessage.

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

End BxeEquitiesLastSaleV15.
